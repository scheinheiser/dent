open Util
open Primitive

type ix = int
type lvl = int
type mv = int

module IM = Map.Make (Int)
module SM = Map.Make (String)

let fresh_i =
  let i = ref (-1) in
  fun () ->
    incr i;
    !i

(* matching patterns *)
type located_pattern = Location.t * pattern

and pattern =
  | PWild (* _ *)
  | PAbs (* . - an impossible pattern *)
  | PConst of const
  | PTypeLit of prim
  | PVar of string
  | PCtor of string * located_pattern list
  | PTuple of located_pattern * located_pattern

(* bound or defined variables *)
type bd =
  | B
  | D

(*NOTE: removed location tracking, might be useful to keep it *)
(* core syntax, tms *)
type tm =
  | Local of string * ix (* local variable as de bruijn index *)
  | Top of string (* reference to a top level function *)
  | Ap of int * tm * tm * icit
  | Mv of mv
  | IMv of mv * bd Snoc.t (* generated mv *)
  | Tuple of tm * tm
  | Let of string * tm * tm * tm (* let p₁ ... pₙ : type = e₁ in e₂ *)
  | Match of tm * (located_pattern * tm) list
    (* match cond to | p₁ when x₁ => y₁ ... | pₙ when xₙ => yₙ*)
  | Lam of string * icit * tm
  | Const of const
  | TypeLit of prim
  | Pi of string * icit * tm * tm (* (α : β) → γ | {α : β} → γ *)

(* values for NbE *)
and val_ =
  | VLam of string * icit * closure
  | VTop of string * spine
  | VLocal of string * lvl * spine
  | VMeta of mv * spine
  | VTuple of val_ * val_
  | VMatch of val_ * env * (located_pattern * tm) list
  | VPi of string * icit * val_ * closure
  | VTypeLit of prim
  | VConst of const

and env = val_ Snoc.t

(* list of variables that a mv or local is applied to *)
and spine = (val_ * icit) Snoc.t

and mv_entry =
  | Solved of val_
  | Unsolved

and closure = env * tm

(* top level extras *)
type located_ty_decl = Location.t * ty_decl
and ty_decl = string * tdecl_type

and tdecl_type =
  | Variant of tm * (string * tm) list
  | Record of string * tm * (string * tm) list

type located_definition = Location.t * definition
and definition = tm * string * tm (* type, identifer, body *)

type program =
  string * located_import list * located_ty_decl list * located_definition list

let mctx : mv_entry IM.t ref = ref IM.empty

let lookup_mv (m : mv) : mv_entry = IM.find m !mctx

let gen_mv bds : tm =
  let mv = fresh_i () in
  mctx := IM.add mv Unsolved !mctx;
  IMv (mv, bds)

(* pretty printing *)
let rec pp_pattern out ((_, arg) : located_pattern) =
  match arg with
  | PConst c -> pp_const out c
  | PTypeLit p -> pp_prim out p
  | PWild -> Format.fprintf out "_"
  | PAbs -> Format.fprintf out "!"
  | PTuple (l, r) -> Format.fprintf out "(%a, %a)" pp_pattern l pp_pattern r
  | PCtor (i, []) -> Format.fprintf out "%s" i
  | PCtor (i, v) ->
    Format.fprintf out "(%s %a)" i
      Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out " ") pp_pattern)
      v
  | PVar i -> Format.fprintf out "%s" i

let wrap_icit icit s =
  match icit with
  | Exp -> Printf.sprintf "( %s )" s
  | Imp -> Printf.sprintf "{ %s }" s

let rec pp_tm out (tm : tm) =
  match tm with
  | Local (i, _) | Top i -> Format.fprintf out "%s" i
  | Const c -> pp_const out c
  | TypeLit p -> pp_prim out p
  | Ap (_, f, arg, icit) ->
    let arg = Format.asprintf "%a" pp_tm arg in
    Format.fprintf out "(@[<hov>%a@ %@ %s@])" pp_tm f (wrap_icit icit arg)
  | Tuple (l, r) -> Format.fprintf out "(%a, %a)" pp_tm l pp_tm r
  | Let (p, ty, v, n) ->
    Format.fprintf out "@[<v 2>let %s : %a =@,%a@]@,in@,%a" p pp_tm ty pp_tm v
      pp_tm n
  | Lam (arg, icit, body) ->
    Format.fprintf out "λ@[<v 2> %s. {@,%a@]@,}" (wrap_icit icit arg) pp_tm body
  | Match (c, bs) ->
    let pp_branch out (p, b) =
      Format.fprintf out "@[(%a) ⇒ %a@]" pp_pattern p pp_tm b
    in
    Format.fprintf out "ma@[<v>tch (%a)@,%a@]" pp_tm c
      Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
      bs
  | Pi (n, icit, l, r) ->
    let l = Format.asprintf "%s : %a" n pp_tm l in
    Format.fprintf out "@[<v>%s -> %a@]" (wrap_icit icit l) pp_tm r
  | Mv m -> Format.fprintf out "?meta%d" m
  | IMv (m, bds) ->
    let to_str bd =
      match bd with
      | B -> "b"
      | D -> "d"
    in
    Format.fprintf out "?meta%d (%s)" m
      (Snoc.map to_str bds
      |> Snoc.fold_left (fun acc v -> Printf.sprintf "%s %s" v acc) "")

let rec pp_val out (v : val_) =
  match v with
  | VTypeLit p -> pp_prim out p
  | VConst c -> pp_const out c
  | VTop (i, sp) -> Format.fprintf out "%s (%s)" i (Snoc.map fst sp |> pp_sp pp_val)
  | VLam (p, icit, cl) -> Format.fprintf out "λ@[<v> %s. {@,%a@]@,}" (wrap_icit icit p) pp_closure cl
  | VTuple (l, r) -> Format.fprintf out "(%a, %a)" pp_val l pp_val r
  | VMatch (c, _, bs) ->
    let pp_branch out (p, b) =
      Format.fprintf out "(%a) ⇒ %a" pp_pattern p pp_tm b
    in
    Format.fprintf out "ma@[<v>tch (%a)@,%a@]" pp_val c
      Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
      bs
  | VPi (n, icit, l, cl) ->
    let l = Format.asprintf "%s : %a" n pp_val l in
    Format.fprintf out "%s -> %a" (wrap_icit icit l) pp_closure cl
  | VLocal (i, _, sp) -> Format.fprintf out "%s (%s)" i (Snoc.map fst sp |> pp_sp pp_val)
  | VMeta (m, sp) -> Format.fprintf out "?meta%d (%s)" m (Snoc.map fst sp |> pp_sp pp_val)

and pp_sp pp_func s =
  let open Snoc in
  let rec go = function
    | Lin -> ""
    | Snoc (Lin, x) -> Format.asprintf "%a" pp_func x
    | Snoc (xs, x) -> Format.asprintf "%a; %s" pp_func x (go xs)
  in
  go s

and pp_closure out ((env, tm) : closure) =
  Format.fprintf out "[ @[<v>%s ] -> @,%a@]" (pp_sp pp_val env) pp_tm tm

let rec pp_ty_decl out ((_, (i, t)) : located_ty_decl) =
  Format.fprintf out "(ty@[<v>pe %s@,%a@])" i pp_tdecl_type t

and pp_tdecl_type out (t : tdecl_type) =
  let pp_field out (i, t) = Format.fprintf out "(%s ~ %a)" i pp_tm t in
  match t with
  | Record (cons, tsig, r) ->
    Format.fprintf out "(re@[<v>cord %s { %a }@,%a@])" cons pp_tm tsig
      Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_field)
      r
  | Variant (tsig, v) ->
    Format.fprintf out "(va@[<v>riant { %a }@,%a@])" pp_tm tsig
      Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_field)
      v

let pp_definition out ((_, (t, f, body)) : located_definition) =
  Format.fprintf out "de@[<v>f %s { %a }@,%a@,@]@.@." f pp_tm t pp_tm body

let pp_module out (mod_name : string) =
  Format.fprintf out "(module %s)" mod_name

let pp_program out ((prog_name, imports, types, body) : program) =
  Format.fprintf out "%a@.@.%a@.@.%a@.@.%a@." pp_module prog_name
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_import)
    imports
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_ty_decl)
    types
    Format.(
      pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_definition)
    body


