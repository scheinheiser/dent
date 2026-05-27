open Util
open Primitive

type located_expr = Location.t * expr

and expr =
  | Tuple of located_expr list
  | Ap of binder * located_expr * located_expr
  (* we give each function a binder to distinguish between user-defined functions and builtins later on *)
  | Let of
      located_pattern
      * located_expr option
      * located_expr
      * located_expr (* let p₁ ... pₙ : <optional_ty> = e₁ in e₂ *)
  | Match of located_expr * (located_pattern * located_expr option * located_expr) list
  | If of located_expr * located_expr * located_expr
  | Lam of located_pattern * located_expr
  | Const of const
  | Var of ident
  | TypeLit of prim
  | Pi of bind option * located_expr * located_expr
  | RCons of string * (string * located_expr) list (* cons { x₁ = y₁; ...; xₙ = yₙ } *)
  | RUpdate of
      string * (string * located_expr) list (* { x where y₁ = z₁; ...; yₙ = zₙ } *)
  | Hole (* _ *)

and bind = string * bool (* identifier, is implicit? *)

type located_ty_decl = Location.t * ty_decl
and ty_decl = string * tdecl_type

and tdecl_type =
  | Alias of located_expr
  | Variant of located_expr * (string * located_expr) list (* type signature and variants *)
  | Record of
      string
      * located_expr
      * (string * located_expr) list (* constructor name, type signature and fields *)

type located_definition = Location.t * definition

and definition =
  | Dec of string * located_expr
  | Def of string * located_pattern list * located_expr option * located_expr * with_block
(* identifer, args, optional when-block, body, optional with-block *)

and with_block = located_definition list

type top_lvl = TDef of located_definition | TTyDecl of located_ty_decl | TImport of located_import
type program = string * located_import list * located_ty_decl list * located_definition list

let rec pp_expr out ((_, e) : located_expr) =
  match e with
  | Var i -> pp_ident out i
  | Const c -> pp_const out c
  | Tuple t ->
      Format.fprintf out "(@[<hov>%a@])"
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out ",@ ") pp_expr)
        t
  | Ap (_, f, arg) -> Format.fprintf out "(@[<hov>%a@ %@ %a@])" pp_expr f pp_expr arg
  | Let (p, ty, v, n) ->
      Format.fprintf out "@[<v>@[<hov>let %a@ = %a@ %a in@]@,%a@]" pp_pattern p
        Format.(pp_print_option ~none:(fun out () -> fprintf out "<none>") pp_expr)
        ty pp_expr v pp_expr n
  | If (cond, tbranch, fbranch) ->
      Format.fprintf out "i@[<v>f %a@,then@ %a@,else@ %a@]" pp_expr cond pp_expr tbranch pp_expr fbranch
  | Lam (arg, body) -> Format.fprintf out "λ @[<v>%a.@,%a@]" pp_pattern arg pp_expr body
  | Match (cond, bs) ->
      let pp_branch out (p, wb, b) =
        Format.fprintf out "(wh@[<v>en %a@,(%a) ⇒ %a@])"
          Format.(pp_print_option ~none:(fun out () -> fprintf out "true") pp_expr)
          wb pp_pattern p pp_expr b
      in
      Format.fprintf out "ma@[<v>tch (%a)@,%a@]" pp_expr cond
        Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
        bs
  | Pi (b, l, r) ->
      let l =
        match b with
        | None -> Format.asprintf "%a" pp_expr l
        | Some (x, false) -> Format.asprintf "(%s : %a)" x pp_expr l
        | Some (x, true) -> Format.asprintf "{%s : %a}" x pp_expr l
      in
      Format.fprintf out "%s -> %a" l pp_expr r
  | TypeLit p -> Format.fprintf out "%a" pp_prim p
  | RCons (i, fields) ->
      let pp_field out (i, v) = Format.fprintf out "%s = %a" i pp_expr v in
      Format.fprintf out "%s @[{ @,%a@] }" i
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "; @,") pp_field)
        fields
  | RUpdate (i, fields) ->
      let pp_field out (i, v) = Format.fprintf out "%s = %a" i pp_expr v in
      Format.fprintf out "{%s wh@[ere@,%a@]}" i
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out ";@,") pp_field)
        fields
  | Hole -> Format.fprintf out "_"


let rec pp_ty_decl out ((_, (i, t)) : located_ty_decl) =
  match t with
  | Alias _ -> Format.fprintf out "(ty@[<v>pe %s %a@])" i pp_tdecl_type t
  | _ -> Format.fprintf out "(ty@[<v>pe %s@,%a@])" i pp_tdecl_type t


and pp_tdecl_type out (t : tdecl_type) =
  let pp_field out ((i, t) : string * located_expr) = Format.fprintf out "(%s %a)" i pp_expr t in
  match t with
  | Alias t -> pp_expr out t
  | Record (cons, tsig, r) ->
      Format.fprintf out "(re@[<v>cord %s { %a }@,%a@])" cons pp_expr tsig
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_field)
        r
  | Variant (tsig, v) ->
      Format.fprintf out "(va@[<v>riant { %a }@,%a@])" pp_expr tsig
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_field)
        v


let pp_when_block out (when_block : located_expr option) =
  Format.fprintf out "%a"
    Format.(
      pp_print_option
        ~none:(fun out () -> fprintf out "()")
        (fun out block -> fprintf out "(when @[<hov>%a@])" pp_expr block))
    when_block


let rec pp_definition out ((_, def) : located_definition) =
  match def with
  | Dec (f, ts) -> Format.fprintf out "(dec %s @[<hov>%a@])" f pp_expr ts
  | Def (f, args, when_block, body, with_block) ->
      Format.fprintf out "(de@[<v>f %s (%a)@,%a@,%a@,%a@])" f
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out " ") pp_pattern)
        args pp_when_block when_block pp_expr body pp_with_block with_block


and pp_with_block out (with_block : with_block) =
  let block out () =
    match with_block with
    | [] -> Format.fprintf out "<none>"
    | _ ->
        Format.fprintf out "%a" Format.(pp_print_list ~pp_sep:pp_print_cut pp_definition) with_block
  in
  Format.fprintf out "(wi@[<v>th@,%a@])" block ()


let pp_module out (mod_name : string) = Format.fprintf out "(module %s)" mod_name

let pp_program out ((prog_name, imports, types, body) : program) =
  Format.fprintf out "%a@.@.%a@.@.%a@.@.%a@." pp_module prog_name
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_import)
    imports
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_ty_decl)
    types
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_definition)
    body
