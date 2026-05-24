(* based on https://github.com/AndrasKovacs/elaboration-zoo *)
open Util
open Primitive

let flip = Fun.flip

(* de bruijn indices and levels *)
type ix = int
type lvl = int

(*NOTE: removed location tracking, might be useful to keep it *)
(* core syntax, tms *)
type tm =
  | Local of ix (* local variable as de bruijn index *)
  | Ap of binder * tm * tm
  (* we give each function a binder to distinguish between user-defined functions and builtins later on *)
  | Tuple of tm list
  | Let of string * tm * tm * tm (* let p₁ ... pₙ : type = e₁ in e₂ *)
  | Match of tm * (located_pattern * tm option * tm) list
    (* match cond to 
       | p₁ when x₁ => y₁
       ...
       | pₙ when xₙ => yₙ*)
  | Lam of string * tm
  | Const of const
  | TypeLit of prim
  | Pi of tm * tm

(* values for NbE *)
type env = val_ list
and closure = env * tm (* local variables in lambdas *)

and val_ =
  | VLocal of lvl (* local variable as de bruijn level *)
  | VLam of string * closure
  | VTuple of val_ list
  | VMatch of val_ * (located_pattern * val_ option * val_) list
  | VPi of val_ * closure
  | VAp of binder * val_ * val_
  | VTypeLit of prim
  | VConst of const

(* top level extras *)
type located_ty_decl = Location.t * ty_decl
and ty_decl = string * tdecl_type

and tdecl_type =
  | Alias of tm
  | Variant of tm * (string * tm) list
  | Record of string * tm * (string * tm) list

type located_definition = Location.t * definition
and definition = tm * string * tm option * tm
(* type, identifer, optional when-block, body, optional with-block *)

type program = string * located_import list * located_ty_decl list * located_definition list

(* early declaration of val/tm for errors *)
let rec pp_tm out (tm : tm) =
  match tm with
  | Local i -> Format.fprintf out "%d" i
  | Const c -> pp_const out c
  | TypeLit p -> pp_prim out p
  | Ap (_, f, arg) -> Format.fprintf out "(%@ @[<hov>%a@ %a@])" pp_tm f pp_tm arg
  | Tuple t ->
      Format.fprintf out "(@[<hov>%a@])"
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out ",@ ") pp_tm)
        t
  | Let (p, ty, v, n) ->
      Format.fprintf out "@[<v>(@[<hov>%s@ %a@ %a@])@,%a@]" p pp_tm ty pp_tm v pp_tm n
  | Lam (arg, body) -> Format.fprintf out "(la@[<v>m (%s)@,%a@])" arg pp_tm body
  | Match (c, bs) ->
      let pp_branch out (p, wb, b) =
        Format.fprintf out "(wh@[<v>en %a@,(%a %a)@])"
          Format.(pp_print_option ~none:(fun out () -> fprintf out "true") pp_tm)
          wb pp_pattern p pp_tm b
      in
      Format.fprintf out "(ma@[<v>tch (%a)@,%a@])" pp_tm c
        Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
        bs
  | Pi (l, r) -> Format.fprintf out "(-> %a %a)" pp_tm l pp_tm r


let rec pp_val out (v : val_) =
  match v with
  | VLocal l -> Format.fprintf out "local_%d" l
  | VLam (p, cl) -> Format.fprintf out "(la@[<v>m (%s)@,%a@])" p pp_closure cl
  | VTuple vs ->
      Format.fprintf out "(%a)"
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out ",@ ") pp_val)
        vs
  | VMatch (c, bs) ->
      let pp_branch out (p, wb, b) =
        Format.fprintf out "(wh@[<v>en %a@,(%a %a)@])"
          Format.(pp_print_option ~none:(fun out () -> fprintf out "true") pp_val)
          wb pp_pattern p pp_val b
      in
      Format.fprintf out "(ma@[<v>tch (%a)@,%a@])" pp_val c
        Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
        bs
  | VPi (l, cl) -> Format.fprintf out "(-> %a %a)" pp_val l pp_closure cl
  | VAp (_, l, r) -> Format.fprintf out "(%@ %a %a)" pp_val l pp_val r
  | VTypeLit p -> pp_prim out p
  | VConst c -> pp_const out c


and pp_closure out ((_, tm) : closure) = pp_tm out tm

(* evaluate a term to a value *)
let rec to_val (env : env) : tm -> val_ = function
  | Local i -> List.nth env i (*NOTE: shouldn't fail unless code is buggy *)
  | TypeLit p -> VTypeLit p
  | Const c -> VConst c
  | Tuple ts -> VTuple (List.map (to_val env) ts)
  | Lam (p, t) -> VLam (p, (env, t))
  | Pi (l, r) -> VPi (to_val env l, (env, r))
  | Ap (b, l, r) -> (
      match (to_val env l, to_val env r) with
      | VLam (_, cl), r -> cl $$ r (* β-reduction *)
      | l, r -> VAp (b, l, r))
  | Match (c, bs) ->
      let c = to_val env c in
      let bs =
        List.map (fun (p, wb, b) -> (p, Base.Option.map ~f:(to_val env) wb, to_val env b)) bs
      in
      VMatch (c, bs)
  | Let (_, _, v, n) ->
      let inner = to_val env v in
      to_val (inner :: env) n


(* applies a closure to a value and evaluates it *)
and ( $$ ) ((env, t) : closure) (v : val_) : val_ = to_val (v :: env) t

(* db level -> db index *)
let to_ix (l : lvl) (r : lvl) = l - r - 1

let rec quote (lvl : lvl) : val_ -> tm = function
  | VLocal l -> Local (to_ix lvl l)
  | VTypeLit t -> TypeLit t
  | VConst c -> Const c
  | VTuple vs -> Tuple (List.map (quote lvl) vs)
  | VAp (b, l, r) -> Ap (b, quote lvl l, quote lvl r)
  | VMatch (c, bs) ->
      let c = quote lvl c in
      let bs =
        List.map (fun (p, wb, b) -> (p, Base.Option.map ~f:(quote lvl) wb, quote lvl b)) bs
      in
      Match (c, bs)
  | VLam (p, cl) ->
      (* increment the level as we move into the closure *)
      (* add a local with the current level to capture the current argument *)
      Lam (p, quote (lvl + 1) (cl $$ VLocal lvl))
  | VPi (l, cl) ->
      let l = quote lvl l in
      let r = quote (lvl + 1) (cl $$ VLocal lvl) in
      Pi (l, r)


(*
  checks if a value can be converted into another, essentially equality.
  carries out β/η conversion.
 *)
let rec conv (lvl : lvl) (l : val_) (r : val_) : bool =
  match (l, r) with
  | VLocal l, VLocal r -> l = r
  | VTypeLit l, VTypeLit r -> l#=r
  | VConst l, VConst r -> l %= r
  | VAp (_, l, r), VAp (_, l', r') -> conv lvl l l' && conv lvl r r'
  | VPi (ll, lc), VPi (rl, rc) ->
      (* go into the closure and check that the bound variables are equal *)
      conv lvl ll rl && conv (lvl + 1) (lc $$ VLocal lvl) (rc $$ VLocal lvl)
  | VLam (_, lc), VLam (_, rc) -> conv (lvl + 1) (lc $$ VLocal lvl) (rc $$ VLocal lvl)
  | VLam (_, cl), r -> 
    (*
       check that applying the right to the captured variable is 
       the same as going into the closure with the captured variable
       (fun x -> M x) N => M N
    *)
    conv (lvl + 1) (cl $$ VLocal lvl) (VAp (0, r, VLocal lvl))
  | l, VLam (_, cl) -> conv (lvl + 1) (VAp (0, l, VLocal lvl)) (cl $$ VLocal lvl)
  | _ -> false


(* type checking *)
type 'a result = 'a Base.Or_error.t

let ( let* ) = Base.Or_error.( >>= )
let ( let@ ) = Base.Or_error.( >>| )

let ( <|> ) l r ctx =
  match l ctx with
  | Ok _ as v -> v
  | Error _ -> r ctx

let combine_errors = Base.Or_error.combine_errors

(* record name, constructor, overall type, field name & type *)
type record_info = string * string * Ast.located_expr * (string * val_) list
type ty = string * val_
type ctx = { env : env; tys : ty list; records : record_info list; lvl : lvl }

let empty_ctx () = { env = []; tys = []; records = []; lvl = 0 }

let bind_var ~(id : string) ~(t : val_) (ctx : ctx) =
  { ctx with env = VLocal ctx.lvl :: ctx.env; tys = (id, t) :: ctx.tys; lvl = ctx.lvl + 1 }


let define_var ~(id : string) ~(v : val_) ~(t : val_) (ctx : ctx) =
  { ctx with env = v :: ctx.env; tys = (id, t) :: ctx.tys; lvl = ctx.lvl + 1 }


let make_err (e : Error.t) : 'a result = Base.Or_error.error_string @@ Error.format_err e
let ok (v : 'a) : 'a result = Ok v

let fresh : string -> string =
  let i = ref (-1) in
  fun s ->
    incr i;
    s ^ string_of_int !i


let replace_pattern ((_, p) : located_pattern) ((loc, _) as b : Ast.located_expr) :
    string * Ast.located_expr =
  match p with
  | PVar i -> (i, b)
  | _ ->
      (* we create a match expr to remove the pattern from the expression *)
      let i = fresh "?p" in
      let match_ =
        let c = (loc, Ast.Var (Ident i)) in
        let branch = [ ((loc, p), None, b) ] in
        (loc, Ast.Match (c, branch))
      in
      (i, match_)


let rec check (ctx : ctx) ((loc, e) : Ast.located_expr) (ex : val_) : tm result =
  match (e, ex) with
  | Ast.Lam (p, b), VPi (l, cl) ->
      let i, b = replace_pattern p b in
      let@ b = check (bind_var ~id:i ~t:l ctx) b (cl $$ VLocal ctx.lvl) in
      Lam (i, b)
  | Ast.Let (p, t, b, n), t' -> (
      let i, b = replace_pattern p b in
      match t with
      | Some t ->
          let* t = is_type ctx t in
          (* check that it's actually a type *)
          let vt = to_val ctx.env t in
          let* b = check ctx b vt in
          let@ n = check (define_var ~id:i ~v:(to_val ctx.env b) ~t:vt ctx) n t' in
          Let (i, t, b, n)
      | None ->
          let* b, t = infer ctx b in
          let@ n = check (define_var ~id:i ~v:(to_val ctx.env b) ~t ctx) n t' in
          let t = quote ctx.lvl t in
          Let (i, t, b, n))
  | e, ex ->
      let* e, t = infer ctx (loc, e) in
      if conv ctx.lvl t ex then ok e
      else
        make_err
          ( Some loc,
            Format.asprintf "Ex@[<v>pected type %a@,but inferred type %a@]" pp_val ex pp_val t )


and infer (ctx : ctx) ((loc, e) : Ast.located_expr) : (tm * val_) result =
  match e with
  | Ast.Const c ->
      let t =
        match c with
        | Int _ -> PInt
        | Float _ -> PFloat
        | String _ -> PString
        | Char _ -> PChar
        | Bool _ -> PBool
        | Unit -> PUnit
      in
      ok @@ (Const c, VTypeLit t)
  | Ast.Tuple es ->
      let@ ets = List.map (infer ctx) es |> combine_errors in
      let es, ts = List.split ets in
      (Tuple es, VTuple ts)
  | Ast.TypeLit p -> ok @@ (TypeLit p, VTypeLit PUni)
  | Ast.If (c, t, f) ->
      let t = ((loc, PConst (Bool true)), None, t) in
      let f = ((loc, PConst (Bool false)), None, f) in
      let e = (loc, Ast.Match (c, [ t; f ])) in
      infer ctx e
  | Ast.Var i -> (
      let i = get_str i in
      let r = List.find_mapi (fun n (x, t) -> if x = i then Some (n, t) else None) ctx.tys in
      match r with
      | None -> make_err (Some loc, Printf.sprintf "Undefined identifier - '%s'." i)
      | Some (n, t) -> ok @@ (Local n, t))
  | Ast.Ap (b, l, r) -> (
      (*TODO: recognise builtins. *)
      let* l, l' = infer ctx l in
      match l' with
      | VPi (l', ret) ->
          let@ r = check ctx r l' in
          (Ap (b, l, r), ret $$ to_val ctx.env r)
          (* β-reduction *)
      | _ ->
          make_err
            (Some loc, Format.asprintf "Ex@[<v>pected a function type@,but inferred %a.@]" pp_val l')
      )
  | Ast.Pi (bind, l, r) -> (
      let* l = is_type ctx l in
      match bind with
      | None ->
          let* r = is_type ctx r in
          ok @@ (Pi (l, r), VTypeLit PUni)
      | Some (i, _) ->
          (* ignoring the type of bind for now. *)
          let l' = to_val ctx.env l in
          let* r = is_type (bind_var ~id:i ~t:l' ctx) r in
          ok @@ (Pi (l, r), VTypeLit PUni))
  | Ast.Let (p, t, b, n) -> (
      let i, b = replace_pattern p b in
      match t with
      | Some t ->
          let* t = is_type ctx t in
          (* check that it's actually a type *)
          let vt = to_val ctx.env t in
          let* b = check ctx b vt in
          let@ n, ty = infer (define_var ~id:i ~v:(to_val ctx.env b) ~t:vt ctx) n in
          (Let (i, t, b, n), ty)
      | None ->
          let* b, t = infer ctx b in
          let@ n, ty = infer (define_var ~id:i ~v:(to_val ctx.env b) ~t ctx) n in
          let t = quote ctx.lvl t in
          (Let (i, t, b, n), ty))
  | Ast.Match (c, bs) ->
      (*TODO: check that the type of the pattern matches the type of the condition *)
      let* c, _ = infer ctx c in
      let check_branch (p, wb, ((loc, _) as b)) =
        let* wb =
          match wb with
          | None -> ok None
          | Some wb ->
              let@ wb = check ctx wb (VTypeLit PBool) in
              Some wb
        in
        let@ b, t = infer ctx b in
        (loc, ((p, wb, b), t))
      in
      let@ bs, t =
        let* bs = List.map check_branch bs |> combine_errors in
        let ex = List.hd bs |> snd |> snd in
        let@ _ =
          List.filter_map
            (fun (loc, (_, t)) ->
              (* if the inferred type is equal, then it's fine *)
              if conv ctx.lvl ex t then None
              else
                Some
                  (make_err
                     ( Some loc,
                       Format.asprintf "Ex@[<v>pected type %a@,but got %a.@]" pp_val ex pp_val t )))
            bs
          |> combine_errors
        in
        (List.map (fun v -> snd v |> fst) bs, ex)
      in
      (Match (c, bs), t)
  | Ast.RCons (cons, fs) -> (
      match List.find_opt (fun (_, c, _, _) -> cons = c) ctx.records with
      | None -> make_err (Some loc, Printf.sprintf "Undefined record constructor - '%s'." cons)
      | Some (_, cons, overall_t, ex_fs) ->
          (* recurses rightward into the type to get the return type *)
          let rec get_t = function Ap (_, _, r) -> get_t r | v -> v in
          let g = List.length fs in
          let e = List.length ex_fs in
          if g <> e then
            make_err
              ( Some loc,
                Format.asprintf
                  "In@[<v>correct amount of record fields.@,\
                   Expected %d field(s).@,\
                   Got %d field(s).@]"
                  e g )
          else
            let* fs =
              (*
                we map over the expected fields, using them to pull the value from the given fields.
                this also ensures that the fields are in the correct order.
              *)
              List.map
                (fun (ex_i, ex_t) ->
                  match List.assoc_opt ex_i fs with
                  | None ->
                      make_err (Some loc, Printf.sprintf "Uninitialised record field - '%s'." ex_i)
                  | Some got -> 
                    Format.fprintf Format.std_formatter "%s: %a@.@." ex_i pp_val ex_t;
                    check ctx got ex_t)
                ex_fs
              |> combine_errors
            in
            let@ ret =
              let@ r = is_type ctx overall_t in
              get_t r |> to_val ctx.env
            in
            let c = 
              let r = List.find_mapi (fun n (x, t) -> if x = cons then Some (n, t) else None) ctx.tys in
              match r with
              | None -> raise (Error.InternalError "Internal error - record constructor not in ctx.")
              | Some (n, _) -> Local n
            in
            (* cons { x₁ = y₁; ...; xₙ = yₙ }  ==> cons y₁ .. yₙ *)
            let cons = List.fold_left (fun n acc -> Ap (0, n, acc)) c fs in
            cons, ret)
  | e -> Error.todo (Format.asprintf "finish infer - %a" Ast.pp_expr (Location.dummy_loc, e))

and is_type (ctx : ctx) (e : Ast.located_expr) : tm result = 
  (* check if it's a type of a type, or one of the builtin types *)
  ((fun ctx -> check ctx e (VTypeLit PUni))
  <|> (fun ctx -> check ctx e (VTypeLit PInt))
  <|> (fun ctx -> check ctx e (VTypeLit PFloat))
  <|> (fun ctx -> check ctx e (VTypeLit PString))
  <|> (fun ctx -> check ctx e (VTypeLit PChar))
  <|> (fun ctx -> check ctx e (VTypeLit PBool))
  <|> (fun ctx -> check ctx e (VTypeLit PUnit))) ctx


let rec check_definition (ctx : ctx) (loc, (i, args, wb, b, locals)) :
    (located_definition list * ctx) result =
  (*
    we go through and typecheck each local definition.
    we first try to find any declared type signatures.
  *)
  let* locals, ctx =
    match locals with
    | [] -> ok ([], ctx)
    | _ ->
        let* ctx =
          let@ ds =
            List.filter_map (function _, Ast.Dec (i, sig_) -> Some (i, sig_) | _ -> None) locals
            |> List.map (fun (i, sig_) ->
                let@ sig_ = is_type ctx sig_ in
                (i, sig_))
            |> combine_errors
          in
          List.fold_left (fun ctx (i, sig_) -> bind_var ~id:i ~t:(to_val ctx.env sig_) ctx) ctx ds
        in
        let rec go ctx acc = function
          | [] -> (List.rev acc, ctx)
          | d :: ds -> (
              match check_definition ctx d with
              | Ok (d, ctx) -> go ctx (Ok d :: acc) ds
              | Error _ as e -> go ctx (e :: acc) ds)
        in
        let r, ctx =
          List.filter_map
            (function
              | loc, Ast.Def (i, args, wb, b, locals) -> Some (loc, (i, args, wb, b, locals))
              | _ -> None)
            locals
          |> go ctx []
        in
        let@ locals = combine_errors r in
        (List.flatten locals, ctx)
  in
  let* wb =
    match wb with
    | None -> ok None
    | Some wb ->
        let* wb = check ctx wb (VTypeLit PBool) in
        ok @@ Some wb
  in
  (*
    we replace any complex pattern (i.e. not just a variable) with a pattern identifier.
    we then construct a match expression with the actual patterns
  *)
  let* b, t =
    match args with
    | [] -> infer ctx b
    | [ p ] ->
        let b = (loc, Ast.Lam (p, b)) in
        infer ctx b
    | ps ->
        let match_ =
          let c =
            let is =
              List.map
                (fun (loc, p) ->
                  match p with
                  | PVar i -> (loc, Ast.Var (Ident i))
                  | _ -> (loc, Ast.Var (Ident (fresh "?p"))))
                ps
            in
            (loc, Ast.Tuple is)
          in
          let bs = [ ((loc, PTuple ps), None, b) ] in
          (loc, Ast.Match (c, bs))
        in
        let b = List.fold_right (fun p acc -> (loc, Ast.Lam (p, acc))) ps match_ in
        infer ctx b
  in
  match List.assoc_opt i ctx.tys with
  | None ->
      let b' = to_val ctx.env b in
      let ctx = define_var ~id:i ~v:b' ~t ctx in
      let t = quote ctx.lvl t in
      let d = (loc, (t, i, wb, b)) in
      ok @@ (d :: locals, ctx)
  | Some t' ->
      if not @@ conv ctx.lvl t' t then
        make_err
          ( Some loc,
            Format.asprintf "Ex@[<v>pected type %a@,But inferred type %a@]" pp_val t' pp_val t )
      else
        let t = quote ctx.lvl t' in
        let d = (loc, (t, i, wb, b)) in
        ok @@ (d :: locals, ctx)


let check_program ((n, mods, tdecls, defs) : Ast.program) : program result =
  let ctx = empty_ctx () in
  let* tdecls, ctx =
    let rec check_decls ctx acc ts =
      (* we check fields/variants in the form of string * located_expr. *)
      let rec check_assoc ?(bind = false) ctx acc as_ =
        match as_ with
        | [] -> (ctx, List.rev acc)
        | (n, t) :: as_ -> (
            match is_type ctx t with
            | Error _ as e -> check_assoc ctx (e :: acc) as_
            | Ok t when bind ->
                let t' = to_val ctx.env t in
                let ctx = bind_var ~id:n ~t:t' ctx in
                check_assoc ctx (Ok (n, t) :: acc) as_
            | Ok t -> 
              check_assoc ctx (Ok (n, t) :: acc) as_)
      in
      match ts with
      | [] -> (ctx, List.rev acc)
      | (loc, (n, Ast.Alias t)) :: ts -> (
          match is_type ctx t with
          | Error _ as e -> check_decls ctx (e :: acc) ts
          | Ok t ->
              let a = (loc, (n, Alias t)) in
              let t = to_val ctx.env t in
              check_decls (bind_var ~id:n ~t ctx) (Ok a :: acc) ts)
      | (loc, (n, Ast.Variant (sig_, vs))) :: ts -> (
          let sig_ = is_type ctx sig_ in
          (* we bind variants so that they become 'functions' *)
          match sig_ with
          | Error _ as e -> check_decls ctx (e :: acc) ts
          | Ok sig_ ->
            let sig_' = to_val ctx.env sig_ in
            (* 
               we bind before checking variants to allow reference to the union type in variants 
               i.e. | ( :: ) : (a : Type) -> List a -> List a
            *)
            let ctx = bind_var ~id:n ~t:sig_' ctx in
            let ctx, vs = check_assoc ~bind:true ctx [] vs in
            match combine_errors vs with
            | (Error _ as e) -> check_decls ctx (e :: acc) ts
            | Ok vs ->
                let v = (loc, (n, Variant (sig_, vs))) in
                check_decls ctx (Ok v :: acc) ts)
      | (loc, (n, Ast.Record (cons, sig_'', fs))) :: ts -> (
          (* gather all record fields and make an ap *)
          let sig_ = is_type ctx sig_'' in
          match sig_ with
          | Error _ as e -> check_decls ctx (e :: acc) ts
          | Ok sig_ ->
            let ctx = bind_var ~id:n ~t:(to_val ctx.env sig_) ctx in
            let ctx, fs = check_assoc ctx [] fs in
            match combine_errors fs with
            | Error _ as e -> check_decls ctx (e :: acc) ts
            | Ok fs ->
                let csig =
                  List.fold_left
                    (fun acc (_, n) -> Pi (n, acc))
                    sig_
                    fs
                in
                let ctx = bind_var ~id:cons ~t:(to_val ctx.env csig) ctx in
                let r = (loc, (n, Record (cons, sig_, fs))) in
                let ctx =
                  (* we hold the record information for checking Ast.RCons and Ast.RUpdate *)
                  let fs = List.map (fun (i, t) -> (i, to_val ctx.env t)) fs in
                  { ctx with records = (n, cons, sig_'', fs) :: ctx.records }
                in
                check_decls ctx (Ok r :: acc) ts)
    in
    let ctx, tdecls = check_decls ctx [] tdecls in
    let@ tdecls = combine_errors tdecls in
    (tdecls, ctx)
  in
  let* ctx =
    let rec go ctx = function
      | [] -> Ok ctx
      | (i, t) :: ts ->
          (*NOTE: 
            inferring here allows you to have a type signature that includes a record, but fails on basic types like Int. 
              - it means that the actual type of the record is given, but the type of primitive (PUni) is given.
            checking if it's a type allows basic types, but fails on records. 
              - it means that the basic type is given, but the actual type of the record is discarded for its identifier.
          *)
          let* _, t = infer ctx t in
          (* let t' = to_val ctx.env t in *)
          go (bind_var ~id:i ~t ctx) ts
    in
    let decs = List.filter_map (function _, Ast.Dec (i, t) -> Some (i, t) | _ -> None) defs in
    go ctx decs
  in
  let@ defs =
    let defs =
      List.filter_map
        (function
          | loc, Ast.Def (i, as_, wb, b, wb') -> Some (loc, (i, as_, wb, b, wb')) | _ -> None)
        defs
    in
    let rec go ctx acc = function
      | [] -> acc
      | d :: ds -> (
          match check_definition ctx d with
          | Error _ as e -> go ctx (e :: acc) ds
          | Ok (d, ctx) -> go ctx (Ok d :: acc) ds)
    in
    go ctx [] defs |> combine_errors
  in
  (n, mods, tdecls, List.flatten defs)


(* pretty printing *)
let rec pp_ty_decl out ((_, (i, t)) : located_ty_decl) =
  match t with
  | Alias _ -> Format.fprintf out "(ty@[<v>pe %s %a@])" i pp_tdecl_type t
  | _ -> Format.fprintf out "(ty@[<v>pe %s@,%a@])" i pp_tdecl_type t


and pp_tdecl_type out (t : tdecl_type) =
  let pp_field out (i, t) = Format.fprintf out "(%s %a)" i pp_tm t in
  match t with
  | Alias t -> pp_tm out t
  | Record (cons, tsig, r) ->
      Format.fprintf out "(re@[<v>cord %s { %a }@,%a@])" cons pp_tm tsig
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_field)
        r
  | Variant (tsig, v) ->
      Format.fprintf out "(va@[<v>riant { %a }@,%a@])" pp_tm tsig
        Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_field)
        v


let pp_when_block out (when_block : tm option) =
  Format.fprintf out "%a"
    Format.(
      pp_print_option
        ~none:(fun out () -> fprintf out "()")
        (fun out block -> fprintf out "(when @[<hov>%a@])" pp_tm block))
    when_block


let pp_definition out ((_, (t, f, when_block, body)) : located_definition) =
  Format.fprintf out "(de@[<v>f %s { %a }@,%a@,%a@]@.)" f pp_tm t pp_when_block when_block pp_tm body


let pp_module out (mod_name : string) = Format.fprintf out "(module %s)" mod_name

let pp_program out ((prog_name, imports, types, body) : program) =
  Format.fprintf out "%a@.@.%a@.@.%a@.@.%a@." pp_module prog_name
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_import)
    imports
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_ty_decl)
    types
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@.") pp_definition)
    body
