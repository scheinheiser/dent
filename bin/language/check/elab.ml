(* based on https://github.com/AndrasKovacs/elaboration-zoo *)
open Util
open Primitive
open Core
open Context
open Evaluation
open Parse

let flip = Fun.flip
let id = Fun.id
let ( @> ) = Snoc.( @> )
let ( <@ ) = Snoc.( <@ )
let singleton = Snoc.singleton

(* variable generators *)
let fresh_pattern_var () : string = "pat$" ^ (fresh_i () |> string_of_int)
let fresh_bind_var () : string = "b$" ^ (fresh_i () |> string_of_int)
let fresh_scrut_var () : string = "c_id$" ^ (fresh_i () |> string_of_int)

(* mutable list that holds all of the holes found in source code *)
let holes : (Location.t * (val_ * val_)) list ref = ref []
let add_hole v = holes := v :: !holes

let fmt_holes () =
  let pp_hole out (loc, v) =
    let pp_t out (b, t) =
      match force b with
      | VMeta _ -> (
        match force t with
        | VMeta _ -> Format.fprintf out "{ couldn't be solved }"
        | v -> pp_val out v)
      | v -> pp_val out v
    in
    Format.fprintf out "%a ⇒ %a" Location.pp_location loc pp_t v
  in
  Format.asprintf "Fo@[<v 2>und hole(s):@,%a@]"
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out "@,") pp_hole)
    !holes

(* case analysis *)
type bind = located_pattern * icit
type constr = string * bind * val_ (* m /? pat, ty *)

and clause =
  constr Snoc.t * bind Snoc.t * Ast.located_expr
(* pattern constraints, remaining patterns and body *)

and problem = {
  clauses : clause list;
  target : val_;
}

(* for debugging *)
let pp_constr out (i, (p, icit), t) =
  let p =
    match icit with
    | Exp -> Format.asprintf "%a" pp_pattern p
    | Imp -> Format.asprintf "{ %a }" pp_pattern p
  in
  Format.fprintf out "%s /? %s ~ %a" i p pp_val t

let pp_clause out (cs, ps, _, b) =
  let cs, ps = (Snoc.to_list cs, Snoc.to_list ps) in
  Format.fprintf out "(%a), (%a) ⇒ %a"
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out ", ") pp_constr)
    cs
    Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out ", ") pp_pattern)
    ps Ast.pp_expr b

(* type checking *)
type 'a result = 'a Base.Option.t

let ( let* ) = Base.Option.( >>= )
let ( let@ ) = Base.Option.( >>| )

let err e =
  Log.err e;
  None

let some v = Some v
let combine_errors = Base.Option.all
let combine_errors_unit = Base.Option.all_unit

(*
   partial renaming. the solution to a problem like ?α spine =? t is ?α = λ x₁
   ... xₙ . t, where the solution has a context Δ and the spine has a context Γ.
   we need to rename spine locals so that they're valid within the Δ context,
   which is where partial renaming comes in.
*)
type partial = {
  gamma : lvl;
  delta : lvl;
  subs : lvl IM.t;
}

let extend_pn (p : partial) : partial =
  {
    gamma = p.gamma + 1;
    delta = p.delta + 1;
    subs = IM.add p.gamma p.delta p.subs;
  }

(* computes Γ ↦ Δ *)
let invert_mapping (loc : Location.t) (delta : lvl) (sp : spine) :
    partial result =
  let open Snoc in
  let rec go = function
    | Lin -> some (0, IM.empty)
    | Snoc (sp, (s, _)) -> (
      let* gamma, subs = go sp in
      match force s with
      | VLocal (_, l, Snoc.Lin) -> (
        match IM.mem l subs with
        | true ->
          err (Some loc, "Non-linear bound variable in unification problem.")
        | false -> some (gamma + 1, IM.add l gamma subs))
      | _ -> err (Some loc, "Unbound value in unification problem."))
  in
  let@ gamma, subs = go sp in
  {gamma; delta; subs}

let rename (loc : Location.t) (mv : mv) (p : partial) (v : val_) : tm result =
  let rec go_sp p sp v : tm result =
    let open Snoc in
    match sp with
    | Lin -> some v
    | Snoc (sp, (s, icit)) ->
      let* l = go_sp p sp v in
      let@ r = go p s in
      Ap (0, l, r, icit)
  and go p v : tm result =
    match force v with
    | VMeta (mv', sp) ->
      if mv = mv' then
        err (Some loc, "Found infinite type in unification problem.")
      else
        go_sp p sp (Mv mv')
    | VLocal (i, l, sp) -> (
      match IM.find_opt l p.subs with
      | None -> err (Some loc, Printf.sprintf "Variable '%s' escapes scope." i)
      | Some l -> go_sp p sp (Local (i, to_ix p.gamma l)))
    | VLam (a, icit, cl) ->
      let@ b = go (extend_pn p) (cl $$ VLocal (a, p.delta, Snoc.empty)) in
      Lam (a, icit, b)
    | VPi (n, icit, l, cl) ->
      let* l = go p l in
      let@ r = go (extend_pn p) (cl $$ VLocal (n, p.delta, Snoc.empty)) in
      Pi (n, icit, l, r)
    | VMatch (c, env, bs) ->
      let* c = go p c in
      let@ bs =
        List.map
          (fun (pat, b) ->
            let@ b = eval env b |> go p in
            (pat, b))
          bs
        |> combine_errors
      in
      Match (c, bs)
    | VTuple (l, r) ->
      let* l = go p l in
      let@ r = go p r in
      Tuple (l, r)
    | VConst c -> some @@ Const c
    | VTypeLit p -> some @@ TypeLit p
    | VTop (i, sp) -> go_sp p sp (Top i)
  in
  go p v

let solve (loc : Location.t) (gamma : lvl) (mv : mv) (sp : spine) (rhs : val_) :
    unit result =
  let nest icits v =
    let rec go n icits t =
      let open Snoc in
      match icits with
      | Lin -> t
      | Snoc (icits, icit) -> Lam ("x" ^ string_of_int (n + 1), icit, go (n + 1) icits t)
    in
    go 0 icits v
  in
  let* p = invert_mapping loc gamma sp in
  let@ rhs = rename loc mv p rhs in
  let sol = eval Snoc.empty @@ nest (Snoc.map snd sp |> Snoc.rev) rhs in
  mctx := IM.add mv (Solved sol) !mctx

let rec unify (ctx : ctx) (l : val_) (r : val_) : unit result =
  let bump_lvl ctx = {ctx with lvl = ctx.lvl + 1} in
  let rec unify_sp ctx sp sp' =
    let open Snoc in
    match (sp, sp') with
    | Lin, Lin -> some ()
    | Snoc (sp, (s, _)), Snoc (sp', (s', _)) ->
      let* _ = unify_sp ctx sp sp' in
      unify ctx s s'
    | _ -> err (Some ctx.loc, "Rigid mismatch in unification.")
  in
  match (force l, force r) with
  | VTypeLit l, VTypeLit r when l#=r -> some ()
  | VConst l, VConst r when l %= r -> some ()
  | VTuple (l, r), VTuple (l', r') ->
    let* _ = unify ctx l l' in
    unify ctx r r'
  | VPi (n, icit, l, cl), VPi (n', icit', l', cl') when icit = icit' ->
    (* go into the closure and check that the bound variables are equal *)
    let* _ = unify ctx l l' in
    unify (bump_lvl ctx)
      (cl $$ VLocal (n, ctx.lvl, Snoc.empty))
      (cl' $$ VLocal (n', ctx.lvl, Snoc.empty))
  | VLam (p, _, cl), VLam (p', _, cl') ->
    unify (bump_lvl ctx)
      (cl $$ VLocal (p, ctx.lvl, Snoc.empty))
      (cl' $$ VLocal (p', ctx.lvl, Snoc.empty))
  | VLam (p, icit, cl), t | t, VLam (p, icit, cl) ->
    (*
       check that applying the right to the captured variable is the same as
       going into the closure with the captured variable (fun x -> M x) N => M N
    *)
    unify (bump_lvl ctx)
      (cl $$ VLocal (p, ctx.lvl, Snoc.empty))
      (v_ap t (VLocal (p, ctx.lvl, Snoc.empty)) icit)
  | VMatch (c, env, bs), VMatch (c', env', bs')
    when List.length bs = List.length bs' ->
    let* _ = unify ctx c c' in
    List.map2
      (fun (p, b) (p', b') ->
        (*NOTE: might be a bit weird doing this unification*)
        let* _ = unify_pat ctx p p' in
        unify ctx (eval env b) (eval env' b'))
      bs bs'
    |> combine_errors_unit
  | VLocal (_, ri, sp), VLocal (_, ri', sp') when ri = ri' ->
    unify_sp ctx sp sp'
  | VTop (i, sp), VTop (i', sp') when i = i' -> unify_sp ctx sp sp'
  | VTop (i, sp), t | t, VTop (i, sp) -> (
    match lookup_top i ctx with
    | None -> err (Some ctx.loc, Printf.sprintf "Undefined identifier - '%s'." i)
    | Some (Def (_, b), _) | Some (Alias b, _) ->
      let b = eval Snoc.empty b |> v_ap_sp sp in
      unify ctx b t
    | Some (DCon _, t') | Some (TCon _, t') -> unify ctx t' t
    | Some (RCon _, _) -> Error.todo ""
    | Some (Axiom _, _) ->
      err (Some ctx.loc, Printf.sprintf "The function '%s' has no definition." i))
  | VMeta (mv, sp), VMeta (mv', sp') when mv = mv' -> unify_sp ctx sp sp'
  | VMeta (mv, sp), t | t, VMeta (mv, sp) -> solve ctx.loc ctx.lvl mv sp t
  | l, r -> uni_err (Some ctx.loc) l r

and uni_err loc ex got =
  err
    ( loc,
      Format.asprintf
        "Va@[<v 4>lue unification failed:@,Expected → %a@,Received → %a@,@]"
        pp_val ex pp_val got )

and equal_pat ctx (_, l) (_, r) : bool result =
  match (l, r) with
  | PWild, _ | _, PWild -> Some true
  | PVar _, _ | _, PVar _ -> Some true
  | PConst l, PConst r -> (
    match (l, r) with
    | Int _, Int _
    | Float _, Float _
    | String _, String _
    | Char _, Char _
    | Bool _, Bool _
    | Unit, Unit -> Some true
    | _ -> Some false)
  | PTypeLit l, PTypeLit r when l#=r -> Some true
  | PAbs, PAbs -> Some true
  | PTuple (l, r), PTuple (l', r') ->
    let* l = equal_pat ctx l l' in
    let@ r = equal_pat ctx r r' in
    l && r
  | PCtor (c, _), PCtor (c', _) ->
    let* (dc, _), _ = lookup_dcon c ctx in
    let* (dc', _), _ = lookup_dcon c' ctx in
    if dc <> dc' then
      Some false
    else
      Some true
  | _ -> Some false

and unify_pat ctx l r : unit result =
  let* res = equal_pat ctx l r in
  if res then
    Some ()
  else
    err
      ( Some ctx.loc,
        Format.asprintf
          "Pa@[<v 4>ttern unification failed:@,Expected → %a@,Received → %a@,@]"
          pp_pattern l pp_pattern r )

(*TODO: make patterns for `TCon`s, to allow matching on user-defined types.*)
(*TODO: allow for matching on implicit patterns*)
let rec to_pattern (ctx : ctx) ((loc, e) : Ast.located_expr) :
        located_pattern result =
  let ctx = update_loc loc ctx in
  let rec flatten (_, ap) acc =
    match ap with
    | Ast.Ap (_, rest, (_, s, _)) -> flatten rest (acc @> s)
    | e -> (e, acc)
  in
  let@ p =
    match e with
    | Ast.Hole -> Some PWild
    | Ast.Impossible -> Some PAbs
    | Ast.Const c -> Some (PConst c)
    | Ast.TypeLit t -> Some (PTypeLit t)
    | Ast.Var (Ident i) -> (
       match lookup_top i ctx with
       | None -> Some (PVar i)
       | Some (DCon _, _) -> Some (PCtor (i, []))
          (* let a = arity t in *)
          (* if a = 0 *)
          (* then Some (PCtor (i,[])) *)
          (* else *)
          (*   err (Some ctx.loc, Format.asprintf "Ex@[<v 4>pected %d args:@,Received → 0 args.@]@." a) *)
       | _ ->
          err (Some ctx.loc, Format.asprintf "Ex@[<v 2>pected a type constructor:@,Received → %s@]" i))
    | Ast.Tuple (l, r) ->
      let* l = to_pattern ctx l in
      let@ r = to_pattern ctx r in
      PTuple (l, r)
    | Ast.RCons (cons, fs) ->
      let* _, ex_fs, _ = lookup_rcon cons ctx in
      let@ fs =
        List.map
          (fun (i, _) ->
            match List.find_opt (fun (i', _) -> i = i') fs with
            | Some (_, p) ->
              (*TODO: check that the pattern is the right type for the field. *)
              to_pattern ctx p
            | None -> Some (loc, PWild))
          ex_fs
        |> combine_errors
      in
      PCtor (cons, fs)
    | Ast.Ap (_, _, _) as ap -> (
      let base, args = flatten (loc, ap) Snoc.empty in
      match base with
      | Ast.Var (Ident i) -> (
         match lookup_top i ctx with
         | None -> err (Some ctx.loc, Printf.sprintf "Undefined identifier - '%s'.\n" i)
         | Some (DCon _, _) ->
            let@ ps =
              List.map (to_pattern ctx) (Snoc.to_list args) |> combine_errors
            in
            PCtor (i, ps)
         | Some _ -> err (Some ctx.loc, Format.asprintf "Ex@[<v 2>pected a type constructor:@,Received → %s@]" i))
      | e ->
        err
          ( Some ctx.loc,
            Format.asprintf
              "Ex@[<v 2>pected a type constructor:@,Received → %a@]@."
              Ast.pp_expr (loc, e) ))
    | e ->
      err
        ( Some ctx.loc,
          Format.asprintf "Ex@[<v 2>pected a pattern:@,Received → %a@]@."
            Ast.pp_expr (loc, e) )
  in
  (loc, p)

let rec insert (ctx : ctx) (infer_res : (tm * val_) result) : (tm * val_) result =
  let* t, tty = infer_res in
  match t with
  | Lam (_, Imp, _) -> some (t, tty)
  | _ -> insert_aux ctx infer_res
and insert_aux (ctx : ctx) (infer_res : (tm * val_) result) : (tm * val_) result =
  let* t, tty = infer_res in
  let rec go (t, tty) =
    match force tty with
    | VPi (_, Imp, _, cl) ->
       let meta = gen_mv ctx.bds in
       go (Ap (0, t, meta, Imp), cl $$ eval ctx.env meta)
    | _ -> some (t, tty)
  in
  go (t, tty)

let insert_until_name (ctx: ctx) (n : string) (infer_res : (tm * val_) result) : (tm * val_) result =
  let* t, tty = infer_res in
  let rec go (t, tty) =
    match force tty with
    | VPi (n', Imp, _, cl) ->
       if n = n'
       then some (t, tty)
       else
         let meta = gen_mv ctx.bds in
         go (Ap (0, t, meta, Imp), cl $$ eval ctx.env meta)
    | _ -> err (Some ctx.loc, Printf.sprintf "Failed to find implicit identifier - '%s'.\n" n)
  in go (t, tty)

let replace_pattern ((_, p) : Ast.located_expr)
    ((loc, _) as b : Ast.located_expr) (icit: icit) : string * Ast.located_expr =
  match p with
  | Ast.Var (Ident i) -> (i, b)
  | _ ->
    (* we create a match expr to remove the pattern from the expression *)
    let i = fresh_pattern_var () in
    let match_ =
     let c = (loc, Ast.Var (Ident i)) in
      let branch = [(((loc, p), icit), b)] in
      (loc, Ast.Match (c, branch))
    in
    (i, match_)

let rec check (ctx : ctx) ((loc, e) : Ast.located_expr) (ex : val_) : tm result
    =
  let ctx = update_loc loc ctx in
  match (e, force ex) with
  | Ast.Lam ((n, p, icit), b), VPi (n', icit', l, cl) when icit = icit' && n = n' ->
    let i, b = replace_pattern p b icit in
    let@ b =
      check (bind_var ~id:i ~t:l ctx) b (cl $$ VLocal (i, ctx.lvl, Snoc.empty))
    in
    Lam (i, icit, b)
  | t, VPi (n, icit, l, cl) ->
     let@ b = check (bind_var ~id:n ~t:l ctx) (loc, t) (cl $$ VLocal (n, ctx.lvl, Snoc.empty)) in
     Lam (n, icit, b)
  | Ast.If (c, t, f), t' ->
    let t = (((loc, Ast.Const (Bool true)), Exp), t) in
    let f = (((loc, Ast.Const (Bool false)), Exp), f) in
    let e = (loc, Ast.Match (c, [t; f])) in
    check ctx e t'
  | Ast.Let (p, t, b, n), t' -> (
    let i, b = replace_pattern p b Exp in
    match t with
    | Some t ->
      let* t, _ = is_type ctx t in
      let vt = eval ctx.env t in
      let* b = check ctx b vt in
      let@ n = check (define_var ~id:i ~v:(eval ctx.env b) ~t:vt ctx) n t' in
      Let (i, t, b, n)
    | None ->
      let* b, t = infer ctx b in
      let@ n = check (define_var ~id:i ~v:(eval ctx.env b) ~t ctx) n t' in
      let t = quote ctx.lvl t in
      Let (i, t, b, n))
  | Ast.Match (c, bs), t' ->
    let* c, t = infer ctx c in
    let c_id = fresh_scrut_var () in
    let* cs =
      List.map
        (fun ((p, icit), b) ->
          let@ p = to_pattern ctx p in
          (singleton (c_id, (p, icit), t), Snoc.empty, b))
        bs
      |> combine_errors
    in
    let ctx = bind_var ~id:c_id ~t ctx in
    let@ ctree = build_tree ctx {clauses = cs; target = t'} in
    Let (c_id, quote 0 t, c, ctree)
  | e, ex ->
    let* e, t = insert ctx @@ infer ctx (loc, e) in
    let@ _ = unify ctx t ex in
    e

and infer (ctx : ctx) ((loc, e) : Ast.located_expr) : (tm * val_) result =
  let get_record_id = function
    | VTop (i, _) -> Some i
    | t ->
      err
        ( Some loc,
          Format.asprintf
            "Expected an identifier with a record type, but got %a." pp_val t )
  in
  let ctx = update_loc loc ctx in
  match e with
  | Ast.TypeLit p ->
    let l =
      match p with
      | PUni n -> n + 1
      | _ -> 0
    in
    some (TypeLit p, VTypeLit (PUni l))
  | Ast.Hole ->
    let t = eval ctx.env @@ gen_mv ctx.bds in
    let a = gen_mv ctx.bds in
    add_hole (loc, (eval ctx.env a, t));
    some (a, t)
  | Ast.Annot (e, t) ->
    let* t, _ = is_type ctx t in
    let t = eval ctx.env t in
    let@ e = check ctx e t in
    (e, t)
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
    some (Const c, VTypeLit t)
  | Ast.Tuple (l, r) ->
    let* l, lt = infer ctx l in
    let@ r, rt = infer ctx r in
    (Tuple (l, r), VTuple (lt, rt))
  | Ast.Var (Ident i) -> (
    match lookup_top i ctx with
    | Some (DCon (_, b), t) -> some (b, t)
    | Some (Alias base, t) -> some (base, t)
    | Some (Def (true, b), t) -> some (b, t) (* an inlined function *)
    | Some (_, t) -> some (Top i, t)
    | None ->
      let@ n, t = lookup_local i ctx in
      (Local (i, n), t))
  | Ast.Var (AccessIdent (base, is)) ->
    let rec final_field_ty r_fields = function
      | [] ->
        Error.internal "base access identifier missing preceding identifiers."
      | [i] ->
        let@ t = List.assoc_opt i r_fields in
        eval Snoc.empty t
      | i :: is ->
        let* t = List.assoc_opt i r_fields in
        let* i = get_record_id @@ eval Snoc.empty t in
        let* _, fields, _ =
          let* cons, _ = lookup_tcon i ctx in
          lookup_rcon (List.hd cons) ctx
        in
        final_field_ty fields is
    in
    let* n, t = lookup_local base ctx in
    let* ri = get_record_id t in
    let* _, r_fields, _ =
      let* cons, _ = lookup_tcon ri ctx in
      lookup_rcon (List.hd cons) ctx
    in
    let@ t = final_field_ty r_fields is in
    let i = Printf.sprintf "%s.%s" base (String.concat "." is) in
    Log.dbg None (Format.asprintf "%s := %a@." i pp_val t);
    (Local (i, n), t)
  | Ast.Lam ((n, x, icit), t) when n = "_" (* can't infer a named lambda *) ->
    let x, t = replace_pattern x t icit in
    let a = eval ctx.env @@ gen_mv ctx.bds in
    let@ t, b = insert ctx @@ infer (bind_var ~id:x ~t:a ctx) t in
    let b = (ctx.env, quote (ctx.lvl + 1) b) in
    (Lam (x, icit, t), VPi (x, icit, a, b))
  | Ast.Ap (b, l, (n, r, icit)) ->
    (*TODO: recognise builtins. *)
    let* icit, l, lt =
      match n, icit with
      | "_", Imp ->
         let@ l, lt = infer ctx l in
         Imp, l, lt
      | "_", Exp ->
         let@ l, lt = insert ctx @@ infer ctx l in
         Exp, l, lt
      | n, Imp ->
         let@ l, lt = insert_until_name ctx n @@ infer ctx l in
         Imp, l, lt
      (*TODO: maybe use this to implement named arguments??*)
      | _ -> Error.internal "can't have a named explicit argument."
    in
    let* lt, ret =
      match force lt with
      | VPi (_, icit', lt, ret) ->
         if icit = icit'
         then some (lt, ret)
         else err (Some ctx.loc, Printf.sprintf "Fo@[<v 2>und an icity mismatch:@,Expected → %s@,Received → %s@]" (show_icit icit') (show_icit icit))
      | lt ->
        let lt' = eval ctx.env @@ gen_mv ctx.bds in
        let r' = (ctx.env, gen_mv (bind_var ~id:"x" ~t:lt ctx).bds) in
        let@ _ = unify ctx (VPi ("x", icit, lt', r')) lt in
        (lt', r')
    in
    Log.dbg None (Format.asprintf "r := %a@." Ast.pp_expr r);
    let@ r = check ctx r lt in
    Log.dbg None
      (Format.asprintf "ap → %a@.ty → %a@." pp_tm (Ap (b, l, r, icit)) pp_closure ret);
    (Ap (b, l, r, icit), ret $$ eval ctx.env r)
  | Ast.Pi ((i, l, icit), r) ->
    let* l, n = is_type ctx l in
    let ctx = bind_var ~id:i ~t:(eval ctx.env l) ctx in
    let@ r, n' = is_type ctx r in
    let n = Int.max n n' in
    (Pi (i, icit, l, r), VTypeLit (PUni n))
  | Ast.Let (p, t, b, n) -> (
    let i, b = replace_pattern p b Exp in
    match t with
    | Some t ->
      let* t, _ = is_type ctx t in
      let vt = eval ctx.env t in
      let* b = check ctx b vt in
      let@ n, ty = infer (define_var ~id:i ~v:(eval ctx.env b) ~t:vt ctx) n in
      (Let (i, t, b, n), ty)
    | None ->
      let* b, t = infer ctx b in
      let@ n, ty = infer (define_var ~id:i ~v:(eval ctx.env b) ~t ctx) n in
      let t = quote ctx.lvl t in
      (Let (i, t, b, n), ty))
  | Ast.RCons (cons, fs) ->
    let* tcon, ex_fs, _ = lookup_rcon cons ctx in
    let got = List.length fs in
    let ex = List.length ex_fs in
    if got <> ex then
      err
        ( Some loc,
          Format.asprintf
            "In@[<v>correct amount of record fields.@,\
             Expected %d field(s).@,\
             Got %d field(s).@]"
            ex got )
    else
      let@ fs =
        List.map
          (fun (ex_i, ex_t) ->
            match List.assoc_opt ex_i fs with
            | None ->
              err
                ( Some loc,
                  Printf.sprintf "Uninitialised record field - '%s'." ex_i )
            | Some got -> check ctx got (eval Snoc.empty ex_t))
          ex_fs
        |> combine_errors
      in
      let e = List.fold_left (fun n acc -> Ap (0, n, acc, Exp)) (Top cons) fs in
      (*TODO: handle parameterised records, i.e. MyRec α *)
      (e, VTop (tcon, Snoc.empty))
  | Ast.RUpdate (base, fs) ->
    let lookup_ri id ctx =
      let* cons, t = lookup_tcon id ctx in
      let@ cons, fs, _ = lookup_rcon (List.hd cons) ctx in
      (cons, fs, t)
    in
    let* n, t = lookup_local base ctx in
    let* ri = get_record_id t in
    let* cons, ex_fs, ret = lookup_ri ri ctx in
    let@ fs =
      List.map
        (fun (ex_i, ex_t) ->
          let ex_t = eval Snoc.empty ex_t in
          match List.find_opt (fun (_, i, _) -> i = ex_i) fs with
          | None ->
            let i = base ^ "." ^ ex_i in
            some @@ Local (i, n)
          | Some (Ast.Assign, _, e) -> check ctx e ex_t
          | Some (Ast.Apply, _, ((loc, _) as f)) ->
            (* { x where y =@ f } ⇒ { x where y := f x.y } *)
            let field = (loc, Ast.Var (AccessIdent (base, [ex_i]))) in
            let v = (loc, Ast.Ap (0, f, ("_", field, Exp))) in
            check ctx v ex_t)
        ex_fs
      |> combine_errors
    in
    let e = List.fold_left (fun n acc -> Ap (0, n, acc, Exp)) (Top cons) fs in
    (e, ret)
  | e -> Error.todo (Format.asprintf "finish infer - %a" Ast.pp_expr (loc, e))

and infer_universe ctx = function
  | VTypeLit (PUni n) -> Some n
  | VTypeLit _ | VMeta _ -> Some 0
  | VTuple (l, r) ->
    let* n = infer_universe ctx l in
    let@ n' = infer_universe ctx r in
    Int.max n n'
  | VTop (i, _) -> (
    match lookup_top i ctx with
    | None ->
      err (Some ctx.loc, Printf.sprintf "Undefined identifier - '%s'\n" i)
    | Some (_, t) ->
      Log.dbg None (Format.asprintf "t := %a@." pp_val t);
      infer_universe ctx t)
  | v ->
    err (Some ctx.loc, Format.asprintf "Expected a Type, but got %a." pp_val v)

and is_type (ctx : ctx) (e : Ast.located_expr) : (tm * int) result =
  let* t, tty = infer ctx e in
  let@ n = infer_universe ctx tty in
  (t, n)

and build_tree (ctx : ctx) (prob : problem) : tm result =
  let collect_dcons ctx tcon =
    let@ dcons, _ = lookup_tcon tcon ctx in
    dcons
  in
  let lookup_con loc i ctx =
    match lookup_top i ctx with
    | None -> err (Some loc, Printf.sprintf "Undefined identifier - '%s'\n" i)
    | Some (DCon (i, _), ty) | Some (RCon (i, _), ty) -> Some (i, ty)
    | Some _ ->
      err
        ( Some loc,
          Printf.sprintf "Expected type/record constructor, but got '%s'.\n" i
        )
  in
  let rec find_split cs =
    let open Snoc in
    match cs with
    | Lin -> None
    | Snoc (_, ((_, ((_, PCtor _), _), _) as c))
    | Snoc (_, ((_, ((_, PConst _), _), _) as c)) -> Some c
    | Snoc (cs, _) -> find_split cs
  in
  let rec done_ ctx target constrs body =
    let open Snoc in
    let rec rename_expr prev new_ (loc, e) =
      let rename = rename_expr prev new_ in
      match e with
      | Ast.Var i when get_str i = prev -> (loc, Ast.Var (Ident new_))
      | Ast.Let (i, ty, b, n) ->
        let ty = Base.Option.map ~f:rename ty in
        let b = rename b in
        let n = rename n in
        (loc, Ast.Let (i, ty, b, n))
      | Ast.Tuple (l, r) -> (loc, Ast.Tuple (rename l, rename r))
      | Ast.Ap (b, l, (n, r, icit)) -> (loc, Ast.Ap (b, rename l, (n, rename r, icit)))
      | Ast.Match (sc, bs) ->
        let bs =
          List.map
            (fun (p, b) -> (p, rename b))
            bs
        in
        (loc, Ast.Match (rename sc, bs))
      | Ast.If (c, t, f) -> (loc, Ast.If (rename c, rename t, rename f))
      | Ast.Lam (p, b) -> (loc, Ast.Lam (p, rename b))
      | Ast.Pi ((n, l, i), r) -> (loc, Ast.Pi ((n, rename l, i), rename r))
      | Ast.RCons (cons, fs) ->
        let fs = List.map (fun (i, e) -> (i, rename e)) fs in
        (loc, Ast.RCons (cons, fs))
      | Ast.RUpdate (i, fs) ->
        let fs = List.map (fun (upd, i, e) -> (upd, i, rename e)) fs in
        (loc, Ast.RUpdate (i, fs))
      | Ast.Annot (e, t) -> (loc, Ast.Annot (rename e, rename t))
      | _ -> (loc, e)
    in
    match constrs with
    | Lin -> check ctx body target
    | Snoc (cs, (_, ((_, PWild), _), _)) -> done_ ctx target cs body
    | Snoc (cs, (new_, ((_, PVar prev), _), _)) ->
       (* rename any occurences of the pattern var with the constr var *)
      let rename = rename_expr prev new_ in
      done_ ctx target cs (rename body)
    | _ -> Error.internal "splittable constraint in done_."
  in
  match (prob.clauses, prob.target) with
  | [], _ -> Error.internal "no cases in build_tree."
  | (_, Snoc.Snoc (_, _), _) :: _, VPi (_, icit, l, cl) ->
    let n = fresh_scrut_var () in
    let r = cl $$ VLocal (n, ctx.lvl, Snoc.empty) in
    let ctx = bind_var ~id:n ~t:l ctx in
    let* clauses =
      List.map
        (fun (constrs, pats, b) ->
          match pats with
          | Snoc.Lin -> err (Some ctx.loc, "Clause size doesn't match.")
          | Snoc.Snoc (ps, p) -> Some (constrs @> (n, p, l), ps, b))
        prob.clauses
      |> combine_errors
    in
    let@ b = build_tree ctx {clauses; target = r} in
    Lam (n, icit, b)
  | (constrs, Snoc.Lin, c_body) :: _, target -> (
    match find_split constrs with
    | None -> done_ ctx target constrs c_body
    | Some (sc, ((loc, p), icit), _) -> (
      let ctx = update_loc loc ctx in
      match p with
      | PCtor (c, _) ->
        let* dcon, _ = lookup_con loc c ctx in
        let clauses_matched_on clauses nm =
          let rec go cs nm acc =
            match cs with
            | [] -> acc
            | (constrs, _, _) :: cs -> (
              match Snoc.find_opt (fun (n, _, _) -> n = nm) constrs with
              | None -> go cs nm acc
              | Some (_, ((_, PCtor (c, _)), icit'), _) when icit = icit' -> go cs nm (c :: acc)
              | Some _ -> go cs nm acc)
          in
          go clauses nm []
        in
        (* | S Z ==> | S (pat$1 ~ Nat) *)
        let push_names ctx dcty =
          (*TODO: figure out to do!!*)
          (* create binding variables over a constructor, using its type sigature *)
          let rec bind_over_pi ctx lvl pi ps acc =
            match (ps, pi) with
            | p :: ps, VPi (n, icit, l, cl) ->
              bind_over_pi (bind_var ~id:p ~t:l ctx) (lvl + 1)
                (cl $$ VLocal (n, lvl, Snoc.empty))
                ps
                (acc @> (p, l, icit))
            | [p], t -> some (bind_var ~id:p ~t ctx, acc @> (p, t, Exp))
            | [], _ ->
              (* Z ~ Nat; no constructors so we don't need to bind anything. *)
              some (ctx, acc)
            | _ ->
              err
                ( Some loc,
                  "Not enough arguments have been applied to the type \
                   constructor." )
          in
          let ps = List.init (arity dcty) (fun _ -> fresh_pattern_var ()) in
          let@ ctx, pts = bind_over_pi ctx ctx.lvl dcty ps Snoc.empty in
          (ctx, pts)
        in
        (* turn a constructor constraint into a set of constraints on its patterns. *)
        let rewrite_constr ctx binds constr dc =
          let rec go ctx binds cs acc =
            match cs with
            | Snoc.Lin -> some acc
            | Snoc.Snoc (cs, ((n, ((loc, p), icit'), _) as constr)) when n = sc -> (
              match p with
              | PConst _ | PTypeLit _ -> Error.internal "splittable in splitted"
              | PCtor (c', old) ->
                let* got, _ = lookup_con loc c' ctx in
                if got <> dcon then
                  err
                    ( Some loc,
                      Printf.sprintf
                        "Expected a constructor from %s, but got a constructor \
                         from %s."
                        dcon got )
                else if dc <> c' || icit <> icit' then
                  None
                else
                  let binds =
                    Snoc.map2
                      (fun (n, t, icit) p -> (n, (p, icit), t))
                      binds (Snoc.of_list old)
                  in
                  some (acc <@ cs <@ binds)
              | _ -> some ((acc <@ cs) @> constr))
            | Snoc.Snoc (cs, c) -> go ctx binds cs (acc @> c)
          in
          go ctx binds constr Snoc.empty
        in
        let* ds = collect_dcons ctx dcon in
        let* hit, missed =
          let matched_on, missed =
            clauses_matched_on prob.clauses sc
            |> List.partition (fun n -> List.exists (( = ) n) ds)
          in
          match missed with
          | [] ->
            List.partition (fun d -> List.exists (( = ) d) matched_on) ds
            |> some
          | cs ->
            let bridge =
              if List.length cs <= 1 then
                "is not a constructor for"
              else
                "aren't constructors for"
            in
            err
              ( Some ctx.loc,
                Printf.sprintf "%s %s %s." (String.concat ", " cs) bridge dcon
              )
        in
        let* sctm =
          let@ n, _ = lookup_local sc ctx in
          Local (sc, n)
        in
        let@ hit =
          let rec build_cases c_acc = function
            | [] -> some c_acc
            | d :: cs ->
              (* builds a case tree for a given constructor *)
              let* _, t = lookup_con loc d ctx in
              let* ctx, pts = push_names ctx t in
              let* clauses =
                List.filter_map
                  (fun (c, ps, b) ->
                    let@ c = rewrite_constr ctx pts c d in
                    Some (c, ps, b))
                  prob.clauses
                |> combine_errors
              in
              let* t = build_tree ctx {clauses; target = prob.target} in
              let args =
                Snoc.map (fun (p, _, _) -> (loc, PVar p)) pts |> Snoc.to_list
              in
              let b = ((loc, PCtor (d, args)), nf ctx t) in
              build_cases (b :: c_acc) cs
          in
          let build_default_case ctx missed =
            (* builds a fallback case for any missing constructors. *)
            let clauses =
              List.filter
                (fun (constrs, _, _) ->
                  match Snoc.find_opt (fun (sc', _, _) -> sc' = sc) constrs with
                  | Some (_, ((_, PWild), _), _) -> true
                  | Some (_, ((_, PVar _), _), _) -> true
                  | None -> true
                  | _ -> false)
                prob.clauses
            in
            (*TODO: print a warning for unused cases. *)
            match clauses with
            | [] ->
              Log.warn
                ( Some ctx.loc,
                  Format.asprintf
                    "Fo@[<v 4>und a non-exhaustive pattern.@,\
                     Missing cases for the constructor(s): %s@.@]"
                    (String.concat ", " missed) );
              let hole = gen_mv ctx.bds in
              add_hole (loc, (eval Snoc.empty hole, prob.target));
              some ((loc, PWild), hole)
            | _ ->
              let@ tree =
                build_tree ctx
                  {clauses = List.rev clauses; target = prob.target}
              in
              ((loc, PWild), nf ctx tree)
          in
          let* bcs = build_cases [] hit in
          match missed with
          | [] -> some bcs
          | _ ->
            let@ def = build_default_case ctx missed in
            bcs @ [def]
        in
        Match (sctm, hit)
      | PConst c ->
        let equal_const l r =
          match (l, r) with
          | Int _, Int _
          | Float _, Float _
          | String _, String _
          | Char _, Char _
          | Bool _, Bool _
          | Unit, Unit -> true
          | _ -> false
        in
        let clauses_matched_on clauses nm =
          let rec go cs nm acc =
            match cs with
            | [] -> acc
            | (constrs, _, _) :: cs -> (
              match Snoc.find_opt (fun (n, _, _) -> n = nm) constrs with
              | None -> go cs nm acc
              | Some (_, ((_, PConst c), icit'), _) when icit = icit' -> go cs nm (c :: acc)
              | Some _ -> go cs nm acc)
          in
          go clauses nm []
        in
        let rewrite_constr ctx constr const =
          let rec go ctx cs acc =
            match cs with
            | Snoc.Lin -> some acc
            | Snoc.Snoc (cs, ((n, ((loc, p), icit'), _) as constr)) when n = sc -> (
              match p with
              | PTypeLit _ | PCtor _ -> Error.internal "splittable in splitted"
              | PConst c' ->
                if not (equal_const const c') then
                  err
                    ( Some loc,
                      Printf.sprintf "Expected %s, but got %s"
                        (show_const const) (show_const c') )
                else if not (const %= c') || icit <> icit' then
                  None
                else
                  some (acc <@ cs)
              | _ -> some ((acc <@ cs) @> constr))
            | Snoc.Snoc (cs, c) -> go ctx cs (acc @> c)
          in
          go ctx constr Snoc.empty
        in
        let* hit =
          let hit, missed =
            clauses_matched_on prob.clauses sc
            |> List.partition (fun c' -> equal_const c c')
          in
          match missed with
          | [] -> some hit
          | lits ->
            let fmt_missed lits =
              List.map (fun c -> Printf.sprintf "a %s" (show_const c)) lits
              |> String.concat ", "
            in
            err
              ( Some loc,
                Printf.sprintf "Expected a %s pattern, but got %s pattern(s)."
                  (show_const c) (fmt_missed lits) )
        in
        let* sctm =
          let@ n, _ = lookup_local sc ctx in
          Local (sc, n)
        in
        let@ cases =
          let rec build_cases c_acc = function
            | [] -> some c_acc
            | const :: cs ->
              let* clauses =
                List.filter_map
                  (fun (constr, ps, b) ->
                    let@ constr = rewrite_constr ctx constr const in
                    Some (constr, ps, b))
                  prob.clauses
                |> combine_errors
              in
              let* t = build_tree ctx {clauses; target = prob.target} in
              let c = ((loc, PConst const), nf ctx t) in
              build_cases (c :: c_acc) cs
          in
          let build_default_case ctx =
            (* create a default, missed value based on the type of constant given. *)
            let get_default cs =
              let fail () = Error.internal "failed to remove unequal consts." in
              match c with
              | Unit -> "()"
              | Bool b -> Printf.sprintf "%B" (not b)
              | String _ ->
                let cs =
                  List.map
                    (function
                      | String s -> s
                      | _ -> fail ())
                    cs
                in
                List.fold_left (fun d s -> if d = s then d ^ "_" else d) "" cs
              | Char _ ->
                let incr c = Char.code c |> ( + ) 1 |> Char.chr in
                let cs =
                  List.map
                    (function
                      | Char c -> c
                      | _ -> fail ())
                    cs
                in
                List.fold_left (fun d s -> if d = s then incr d else d) '_' cs
                |> Char.escaped
              | Float _ ->
                let cs =
                  List.map
                    (function
                      | Float f -> f
                      | _ -> fail ())
                    cs
                in
                List.fold_left (fun d s -> if d = s then 1. +. d else d) 0. cs
                |> string_of_float
              | Int _ ->
                let cs =
                  List.map
                    (function
                      | Int i -> i
                      | _ -> fail ())
                    cs
                in
                List.fold_left (fun d s -> if d = s then d + 1 else d) 0 cs
                |> string_of_int
            in
            let clauses =
              List.filter
                (fun (constrs, _, _) ->
                  match Snoc.find_opt (fun (sc', _, _) -> sc' = sc) constrs with
                  | Some (_, ((_, PWild), icit'), _) | Some (_, ((_, PVar _), icit'), _) when icit = icit' -> true
                  | _ -> false)
                prob.clauses
            in
            match clauses with
            | [] ->
              err
                ( Some loc,
                  Format.asprintf
                    "Fo@[<v 4>und a non-exhaustive pattern.@,\
                     Here is an example of an unmatched case: %S@]@."
                    (get_default hit) )
            | _ ->
              let@ tree =
                build_tree ctx
                  {clauses = List.rev clauses; target = prob.target}
              in
              ((loc, PWild), nf ctx tree)
          in
          let* bcs = build_cases [] hit in
          let@ def = build_default_case ctx in
          bcs @ [def]
        in
        Match (sctm, cases)
      | _ -> Error.internal "unsplittable pattern from find_split."))
  | _ -> Error.todo "bing"

let rec check_definition (ctx : ctx) (loc, (i, args, b, locals)) :
    (located_definition list * ctx) result =
  let* locals, ctx' = check_locals ctx locals in
  let* inline, target = get_target i ctx' in
  let args = insert_implicits args target in
  let clause = (Snoc.empty, Snoc.of_list args, b) in
  let@ b = build_tree ctx' {clauses = [clause]; target} in
  let t = force target in
  let d = (loc, (quote ctx'.lvl t, i, b)) in
  let ctx = define_func ~id:i ~t ~v:(inline, b) ctx in
  (d :: locals, ctx)

and check_flpm ctx ((loc, (i, args, b, locals)) as def) ds =
  let* remaining, matched =
    let rec go failed_acc acc = function
      | [] -> Some (failed_acc, acc)
      | ((_, (i', args', _, _)) as d) :: ds
        when i' = i && List.length args = List.length args' ->
        let* r = List.map2 (fun (l, _) (r, _) -> equal_pat ctx l r) args args' |> combine_errors in
        if List.for_all id r then
          go failed_acc (d :: acc) ds
        else
          go (d :: failed_acc) acc ds
      | d :: ds -> go (d :: failed_acc) acc ds
    in
    go [] [] ds
  in
  let@ ds, ctx =
    match matched with
    | [] -> check_definition ctx def
    | ms' ->
      let ms' = List.rev ms' in
      let ms =
        List.map
          (fun (_, (_, args, b, _)) ->
            (Snoc.empty, Snoc.of_rev_list args, b))
          ms'
      in
      let* locals, ctx' = check_locals ctx locals in
      let* locals', ctx' =
        let rec go acc ctx = function
          | [] -> Some (List.flatten acc, ctx)
          | l :: ls ->
            let* l, ctx = check_locals ctx l in
            go (l :: acc) ctx ls
        in
        go [] ctx' @@ List.map (fun (_, (_, _, _, locals)) -> locals) ms'
      in
      let* inline, target = get_target i ctx' in
      let args = insert_implicits args target in
      let def = (Snoc.empty, Snoc.of_rev_list args, b) in
      let@ b = build_tree ctx' {clauses = def :: ms; target} in
      let t = force target in
      let ctx = define_func ~id:i ~t ~v:(inline, b) ctx in
      let b = (loc, (quote ctx'.lvl t, i, b)) in
      ((b :: locals) @ locals', ctx)
  in
  (ds, ctx, List.rev remaining)

and check_locals ctx locals =
  match locals with
  | [] -> some ([], ctx)
  | _ ->
    let* ctx =
      let@ ds =
        List.filter_map
          (function
            | _, Ast.Dec (inline, i, sig_) -> Some (inline, i, sig_)
            | _ -> None)
          locals
        |> List.map (fun (inline, i, sig_) ->
            let@ sig_, _ = is_type ctx sig_ in
            (inline, i, sig_))
        |> combine_errors
      in
      List.fold_left
        (fun ctx (inline, i, sig_) -> bind_func ~id:i ~t:(eval ctx.env sig_) ~inline ctx)
        ctx ds
    in
    let rec go ctx acc = function
      | [] -> (List.rev acc, ctx)
      | (loc, (i, args, b, locals)) :: ds -> (
        let args = List.map (fun (p, icit) -> let@ p = to_pattern ctx p in p, icit) args |> combine_errors in
        match args with
        | None -> go ctx (None :: acc) ds
        | Some args -> (
          let d = (loc, (i, args, b, locals)) in
          match check_definition ctx d with
          | Some (d, ctx) -> go ctx (Some d :: acc) ds
          | None -> go ctx (None :: acc) ds))
    in
    let r, ctx =
      List.filter_map
        (function
          | loc, Ast.Def (i, args, b, locals) -> Some (loc, (i, args, b, locals))
          | _ -> None)
        locals
      |> go ctx []
    in
    let@ locals = combine_errors r in
    (List.flatten locals, ctx)

and get_target i ctx =
  match lookup_top i ctx with
  | None -> Some (false, eval Snoc.empty @@ gen_mv ctx.bds)
  | Some (Axiom inline, t') -> Some (inline, t')
  | Some (Def _, _) ->
    err
      ( Some ctx.loc,
        Printf.sprintf "The function '%s' has already been defined." i )
  | Some _ ->
    (* shouldn't occur unless it's an operator. *)
     err (Some ctx.loc, Printf.sprintf "The identifier '%s' is already in use." i)

and insert_implicits args target =
    let rec go args target i acc =
    match args, target with
    | [], _ -> acc
    | (((loc, _), Exp) :: _) as args, VPi (n, Imp, _, r) ->
       (* we inject an implicit argument when found *)
       let imp_arg = ((loc, PVar n), Imp) in
       go args (r $$ VLocal (n, i, Snoc.empty)) (i + 1) (imp_arg :: acc)
    | (_, icit) as arg :: args, VPi (n, icit', _, r) when icit = icit' ->
       go args (r $$ VLocal (n, i, Snoc.empty)) (i + 1) (arg :: acc)
    | _ -> Error.internal "implicit argument used where explicit was expected??"
  in
  go args target 0 []

let check_program ((n, mods, tdecls, defs) : Ast.program) : program result =
  let ctx = empty_ctx () in
  let* tdecls, ctx =
    (*TODO: just use let* and let@ rather than trying to catch every error. *)
    let rec check_decls ctx acc ts =
      let pi_to_lam cons pi =
        (* given ( × ) ~ (a : U) → (b: U) → Pair a b *)
        let id_stack =
          let rec go pi acc =
            match pi with
            | Pi (n, icit, _, r) -> go r (acc @> (n, icit))
            | _ -> acc
          in
          go pi Snoc.empty
        in
        (* ( × ) a b ⇒ ( × ) 1 0 *)
        let ap, _ =
          Snoc.fold_left
            (fun (acc, n) (i, icit) -> (Ap (0, acc, Local (i, n), icit), n + 1))
            (Top cons, 0) id_stack
        in
        (* ( × ) 1 0 ⇒ λ λ. ( × ) 1 0 *)
        let v = Snoc.fold_right (fun (i, icit) acc -> Lam (i, icit, acc)) id_stack ap in
        Log.dbg None (Format.asprintf "Turned pi into %a@." pp_tm v);
        v
      in
      let params_to_pi params =
        let ret, _ =
          List.fold_left
            (fun (ap, n) (i, _) -> (Ap (0, ap, Local (i, n), Exp), n + 1))
            (TypeLit (PUni 0), 0) params
        in
        List.fold_right (fun (i, t) acc -> Pi (i, Exp, t, acc)) params ret
      in
      (* we check fields/variants in the form of string * located_expr. *)
      let rec check_assoc ?(bind = ("", false)) ctx acc as_ =
        let i, b = bind in
        match as_ with
        | [] -> (ctx, List.rev acc)
        | (n, t) :: as_ -> (
          match is_type ctx t with
          | None -> check_assoc ctx (None :: acc) as_
          | Some (t, _) when b ->
            let t' = eval Snoc.empty t in
            let v = (i, pi_to_lam n t) in
            let ctx = define_dcon ~id:n ~t:t' ~v ctx in
            check_assoc ctx ~bind (Some (n, t) :: acc) as_
          | Some (t, _) -> check_assoc ctx (Some (n, t) :: acc) as_)
      in
      match ts with
      | [] -> (ctx, List.rev acc)
      | (_, (n, Ast.Alias t)) :: ts -> (
        match is_type ctx t with
        | None -> check_decls ctx (None :: acc) ts
        | Some (v, l) ->
          check_decls
            (define_alias ~id:n ~t:(VTypeLit (PUni l)) ~ty:v ctx)
            acc ts)
      | (loc, (n, Ast.Variant (sig_, vs))) :: ts -> (
        let sig_ = is_type ctx sig_ in
        match sig_ with
        | None -> check_decls ctx (None :: acc) ts
        | Some (sig_, _) -> (
          let ctx =
            define_tcon ~id:n ~t:(eval Snoc.empty sig_)
              ~constrs:(List.map fst vs) ctx
          in
          let ctx, vs = check_assoc ~bind:(n, true) ctx [] vs in
          match combine_errors vs with
          | None -> check_decls ctx (None :: acc) ts
          | Some vs ->
            let v = (loc, (n, Variant (sig_, vs))) in
            check_decls ctx (Some v :: acc) ts))
      | (loc, (tcon, Ast.Record (cons, tvs, fs))) :: ts -> (
        (*TODO: prevent duplicate fields *)
        let ctx, params = check_assoc ctx [] tvs in
        match combine_errors params with
        | None -> check_decls ctx (None :: acc) ts
        | Some params -> (
          let sig_ = params_to_pi params in
          (* bind all parameters before checking the fields *)
          let ctx =
            let ctx =
              define_tcon ~id:tcon ~t:(eval Snoc.empty sig_) ~constrs:[cons] ctx
            in
            List.fold_left
              (fun ctx (id, t) -> bind_var ~id ~t:(eval Snoc.empty t) ctx)
              ctx params
          in
          let ctx, fs = check_assoc ctx [] fs in
          match combine_errors fs with
          | None -> check_decls ctx (None :: acc) ts
          | Some fs ->
            (* build a type signature for the record *)
            let csig =
              List.fold_right
                (fun (_, n) acc -> Pi (fresh_bind_var (), Exp, n, acc))
                fs sig_
            in
            Log.dbg None (Format.asprintf "csig := %a@." pp_tm csig);
            let ctx =
              define_rcon ~id:cons ~t:(eval Snoc.empty csig) ~tcon ~fields:fs
                ctx
            in
            let r = (loc, (n, Record (cons, sig_, fs))) in
            check_decls ctx (Some r :: acc) ts))
    in
    let ctx, tdecls = check_decls ctx [] tdecls in
    let@ tdecls = combine_errors tdecls in
    (tdecls, ctx)
  in
  let* ctx =
    let rec go ctx = function
      | [] -> Some ctx
      | (inline, i, t) :: ts ->
        let* t, _ = is_type ctx t in
        let t = eval Snoc.empty t in
        Log.dbg None (Format.asprintf "%s ↦ %a@." i pp_val t);
        go (bind_func ~id:i ~t ~inline ctx) ts
    in
    let decs =
      List.filter_map
        (function
          | _, Ast.Dec (inline, i, t) -> Some (inline, i, t)
          | _ -> None)
        defs
    in
    go ctx decs
  in
  let* defs =
    let defs =
      List.filter_map
        (function
          | loc, Ast.Def (i, args, b, locals) ->
            Some (loc, (i, args, b, locals))
          | _ -> None)
        defs
    in
    let* defs =
      List.map
        (fun (loc, (i, args, b, locals)) ->
          let@ args = List.map (fun (a, icit) -> let@ a = to_pattern ctx a in a, icit) args |> combine_errors in
          (loc, (i, args, b, locals)))
        defs
      |> combine_errors
    in
    let rec go ctx acc = function
      | [] -> acc
      | d :: ds -> (
        match check_flpm ctx d ds with
        | None -> go ctx (None :: acc) ds
        | Some (d, ctx, ds) -> go (flush_locals ctx) (Some d :: acc) ds)
    in
    go ctx [] defs |> combine_errors
  in
  (*TODO: halt further compilation if a function isn't defined (but has a type signature). *)
  match !holes with
  | [] -> some (n, mods, tdecls, List.rev defs |> List.flatten)
  | _ -> err (None, fmt_holes ())
