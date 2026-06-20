(* based on https://github.com/AndrasKovacs/elaboration-zoo *)
open Util
open Primitive
open Core
open Context
open Evaluation

let flip = Fun.flip
let id = Fun.id
let ( @> ) = Snoc.( @> )
let ( <@ ) = Snoc.( <@ )
let singleton = Snoc.singleton

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

let to_ix (l : lvl) (r : lvl) = l - r - 1

(* val → tm *)
let rec quote (lvl : lvl) (v : val_) : tm =
  match force v with
  | VTypeLit t -> TypeLit t
  | VConst c -> Const c
  | VTop (i, sp) -> quote_sp lvl (Top i) sp
  | VTuple (l, r) -> Tuple (quote lvl l, quote lvl r)
  | VMatch (c, env, bs) ->
    let c = quote lvl c in
    let quote_b env (p, wb, b) =
      let rec build_env env (_, p) l =
        match p with
        | PWild | PTypeLit _ | PConst _ | PAbs -> (env, l)
        | PVar i -> (env @> VLocal (i, l, Snoc.empty), l + 1)
        | PAs (i, p) ->
          let env, l = build_env env p l in
          (env @> VLocal (i, l, Snoc.empty), l + 1)
        | PTuple (l', r) ->
          let env, l = build_env env l' l in
          build_env env r l
        | PCtor (_, args) ->
          let args, l =
            List.fold_left
              (fun (sn, l) n ->
                let sn, l = build_env sn n l in
                (sn, l + 1))
              (env, l) args
          in
          (args, l)
      in
      let env, l = build_env env p lvl in
      let wb = eval env wb |> quote l in
      let b = eval env b |> quote l in
      (p, wb, b)
    in
    let bs = List.map (quote_b env) bs in
    Match (c, bs)
  | VLam (p, cl) ->
    (*
       increment the level as we move past a binder.
       add a local with the current level to capture the argument.
    *)
    Lam (p, quote (lvl + 1) (cl $$ VLocal (p, lvl, Snoc.empty)))
  | VPi (n, l, cl) ->
    let l = quote lvl l in
    let r = quote (lvl + 1) (cl $$ VLocal (n, lvl, Snoc.empty)) in
    Pi (n, l, r)
  | VMeta (m, sp) -> quote_sp lvl (Mv m) sp
  | VLocal (i, l, sp) -> quote_sp lvl (Local (i, to_ix lvl l)) sp

(* unroll a flex/rigid into a set of applications *)
and quote_sp (lvl : lvl) (v : tm) (sp : spine) : tm =
  match sp with
  | Snoc.Lin -> v
  | Snoc.Snoc (sp, s) -> Ap (0, quote_sp lvl v sp, quote lvl s)

(* case analysis *)
type constr = string * located_pattern * val_ (* m /? pat, ty *)

and clause =
  constr Snoc.t * located_pattern Snoc.t * Ast.located_expr * Ast.located_expr
(* pattern constraints, remaining patterns, when-block and body *)

and problem = {
  clauses : clause list;
  target : val_;
}

(* for debugging *)
let pp_constr out (i, p, t) =
  Format.fprintf out "%s /? %a ~ %a" i pp_pattern p pp_val t

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
    | Snoc (sp, s) -> (
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
    | Snoc (sp, s) ->
      let* l = go_sp p sp v in
      let@ r = go p s in
      Ap (0, l, r)
  and go p v : tm result =
    match force v with
    | VMeta (mv', sp) ->
      if mv = mv' then
        err (Some loc, "Found infinite type in unification problem.")
      else
        go_sp p sp (Mv mv')
    | VLocal (i, l, sp) -> (
      match IM.find_opt l p.subs with
      | None ->
        Log.dbg None
          (Format.asprintf "rigid(%d) -> %a@.subs -> %d@." l pp_val (force v)
             (IM.to_list p.subs |> List.length));
        err (Some loc, Printf.sprintf "Variable '%s' escapes scope." i)
      | Some l -> go_sp p sp (Local (i, to_ix p.gamma l)))
    | VLam (a, cl) ->
      let@ b = go (extend_pn p) (cl $$ VLocal (a, p.delta, Snoc.empty)) in
      Lam (a, b)
    | VPi (n, l, cl) ->
      let* l = go p l in
      let@ r = go (extend_pn p) (cl $$ VLocal (n, p.delta, Snoc.empty)) in
      Pi (n, l, r)
    | VMatch (c, env, bs) ->
      let* c = go p c in
      let@ bs =
        List.map
          (fun (pat, wb, b) ->
            let* wb = eval env wb |> go p in
            let@ b = eval env b |> go p in
            (pat, wb, b))
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
  let nest lvl v =
    let rec go n t acc =
      if n = acc then
        t
      else
        Lam ("x" ^ string_of_int (acc + 1), go n t (acc + 1))
    in
    go lvl v 0
  in
  let* p = invert_mapping loc gamma sp in
  Log.dbg None (Format.asprintf "rhs := %a@." pp_val rhs);
  let@ rhs = rename loc mv p rhs in
  let sol = eval Snoc.empty @@ nest p.gamma rhs in
  mctx := IM.add mv (Solved sol) !mctx

(* compute the normal form of a term *)
let nf ctx v = eval ctx.env v |> quote ctx.lvl

let rec unify (ctx : ctx) (l : val_) (r : val_) : unit result =
  let bump_lvl ctx = {ctx with lvl = ctx.lvl + 1} in
  let rec unify_sp ctx sp sp' =
    let open Snoc in
    match (sp, sp') with
    | Lin, Lin -> some ()
    | Snoc (sp, s), Snoc (sp', s') ->
      let* _ = unify_sp ctx sp sp' in
      unify ctx s s'
    | _ ->
      Log.dbg None (Printf.sprintf "sp := %s\n" (pp_sp pp_val sp));
      Log.dbg None (Printf.sprintf "sp' := %s\n" (pp_sp pp_val sp'));
      err (Some ctx.loc, "Rigid mismatch in unification.")
  in
  match (force l, force r) with
  | VTypeLit l, VTypeLit r when l#=r -> some ()
  | VConst l, VConst r when l %= r -> some ()
  | VTuple (l, r), VTuple (l', r') ->
    let* _ = unify ctx l l' in
    unify ctx r r'
  | VPi (n, l, cl), VPi (n', l', cl') ->
    (* go into the closure and check that the bound variables are equal *)
    let* _ = unify ctx l l' in
    unify (bump_lvl ctx)
      (cl $$ VLocal (n, ctx.lvl, Snoc.empty))
      (cl' $$ VLocal (n', ctx.lvl, Snoc.empty))
  | VLam (p, cl), VLam (p', cl') ->
    unify (bump_lvl ctx)
      (cl $$ VLocal (p, ctx.lvl, Snoc.empty))
      (cl' $$ VLocal (p', ctx.lvl, Snoc.empty))
  | VLam (p, cl), t | t, VLam (p, cl) ->
    (*
       check that applying the right to the captured variable is the same as
       going into the closure with the captured variable (fun x -> M x) N => M N
    *)
    unify (bump_lvl ctx)
      (cl $$ VLocal (p, ctx.lvl, Snoc.empty))
      (v_ap t (VLocal (p, ctx.lvl, Snoc.empty)))
  | VMatch (c, env, bs), VMatch (c', env', bs')
    when List.length bs = List.length bs' ->
    (*TODO: unify patterns *)
    let* _ = unify ctx c c' in
    List.map2
      (fun (p, _, b) (p', _, b') ->
        let b = eval env b in
        let b' = eval env' b' in
        let* _ = unify_pat ctx p p' in
        (*NOTE: might be a bit weird doing this unification*)
        unify ctx b b')
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
      err (Some ctx.loc, Printf.sprintf "The function '%s' has no definition." i)
    )
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

let rec to_pattern (ctx : ctx) ((loc, e) : Ast.located_expr) :
    located_pattern result =
  let rec flatten (_, ap) acc =
    match ap with
    | Ast.Ap (_, rest, s) -> flatten rest (acc @> s)
    | e -> (e, acc)
  in
  let@ p =
    match e with
    | Ast.Hole -> Some PWild
    | Ast.Impossible -> Some PAbs
    | Ast.Const c -> Some (PConst c)
    | Ast.TypeLit t -> Some (PTypeLit t)
    | Ast.Var (Ident i) -> Some (PVar i)
    | Ast.Var (Udc i) -> Some (PCtor (i, []))
    | Ast.Tuple (l, r) ->
      let* l = to_pattern ctx l in
      let@ r = to_pattern ctx r in
      PTuple (l, r)
    | Ast.As (i, p) ->
      let@ p = to_pattern ctx p in
      PAs (i, p)
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
      | Ast.Var (Udc i) ->
        let@ ps =
          List.map (to_pattern ctx) (Snoc.to_list args) |> combine_errors
        in
        PCtor (i, ps)
      | e ->
        err
          ( Some loc,
            Format.asprintf
              "Ex@[<v 2>pected a type constructor:@,Received → %a@]@."
              Ast.pp_expr (loc, e) ))
    | e ->
      err
        ( Some loc,
          Format.asprintf "Ex@[<v 2>pected a pattern:@,Received → %a@]@."
            Ast.pp_expr (loc, e) )
  in
  (loc, p)

let fresh_pattern_var () : string = "pat$" ^ (fresh_i () |> string_of_int)
let fresh_bind_var () : string = "b$" ^ (fresh_i () |> string_of_int)
let fresh_scrut_var () : string = "c_id$" ^ (fresh_i () |> string_of_int)

let replace_pattern ((_, p) : Ast.located_expr)
    ((loc, _) as b : Ast.located_expr) : string * Ast.located_expr =
  match p with
  | Ast.Var (Ident i) -> (i, b)
  | _ ->
    (* we create a match expr to remove the pattern from the expression *)
    let i = fresh_pattern_var () in
    let match_ =
      let c = (loc, Ast.Var (Ident i)) in
      let branch = [((loc, p), None, b)] in
      (loc, Ast.Match (c, branch))
    in
    (i, match_)

let rec check (ctx : ctx) ((loc, e) : Ast.located_expr) (ex : val_) : tm result
    =
  let ctx = update_loc loc ctx in
  match (e, force ex) with
  | Ast.Lam (p, b), VPi (_, l, cl) ->
    let i, b = replace_pattern p b in
    let@ b =
      check (bind_var ~id:i ~t:l ctx) b (cl $$ VLocal (i, ctx.lvl, Snoc.empty))
    in
    Lam (i, b)
  | Ast.If (c, t, f), t' ->
    let t = ((loc, Ast.Const (Bool true)), None, t) in
    let f = ((loc, Ast.Const (Bool false)), None, f) in
    let e = (loc, Ast.Match (c, [t; f])) in
    check ctx e t'
  | Ast.Let (p, t, b, n), t' -> (
    let i, b = replace_pattern p b in
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
        (fun (p, wb, ((loc, _) as b)) ->
          let wb =
            match wb with
            | None -> (loc, Ast.Const (Bool true))
            | Some wb -> wb
          in
          let@ p = to_pattern ctx p in
          (singleton (c_id, p, t), Snoc.empty, wb, b))
        bs
      |> combine_errors
    in
    let ctx = bind_var ~id:c_id ~t ctx in
    let@ ctree = build_tree ctx {clauses = cs; target = t'} in
    Let (c_id, quote 0 t, c, ctree)
  | e, ex ->
    let* e, t = infer ctx (loc, e) in
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
    let* e, t' = infer ctx e in
    let@ _ = unify ctx t t' in
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
  | Ast.Var (Ident i) | Ast.Var (Udc i) -> (
    match lookup_top i ctx with
    | Some (DCon (_, b), t) -> some (b, t)
    | Some (Alias base, t) -> some (base, t)
    | Some (Def (true, b), t) -> some (b, t)
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
  | Ast.Lam (x, t) ->
    let x, t = replace_pattern x t in
    let a = eval ctx.env @@ gen_mv ctx.bds in
    let@ t, b = infer (bind_var ~id:x ~t:a ctx) t in
    let b = (ctx.env, quote (ctx.lvl + 1) b) in
    (Lam (x, t), VPi (x, a, b))
  | Ast.Ap (b, l, r) ->
    (*TODO: recognise builtins. *)
    Log.dbg None (Format.asprintf "l := %a@." Ast.pp_expr l);
    let* l, lt = infer ctx l in
    let* lt, ret =
      match force lt with
      | VPi (_, lt, ret) -> some (lt, ret)
      | lt ->
        let lt' = eval ctx.env @@ gen_mv ctx.bds in
        let r' = (ctx.env, gen_mv (bind_var ~id:"x" ~t:lt ctx).bds) in
        let@ _ = unify ctx (VPi ("x", lt', r')) lt in
        (lt', r')
    in
    Log.dbg None (Format.asprintf "r := %a@." Ast.pp_expr r);
    let@ r = check ctx r lt in
    Log.dbg None
      (Format.asprintf "ap → %a@.ty → %a@." pp_tm (Ap (b, l, r)) pp_closure ret);
    (Ap (b, l, r), ret $$ eval ctx.env r)
  | Ast.Pi ((i, _), l, r) ->
    let* l, n = is_type ctx l in
    let ctx = bind_var ~id:i ~t:(eval ctx.env l) ctx in
    let@ r, n' = is_type ctx r in
    let n = Int.max n n' in
    (Pi (i, l, r), VTypeLit (PUni n))
  | Ast.Let (p, t, b, n) -> (
    let i, b = replace_pattern p b in
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
      let e = List.fold_left (fun n acc -> Ap (0, n, acc)) (Top cons) fs in
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
            let v = (loc, Ast.Ap (0, f, field)) in
            check ctx v ex_t)
        ex_fs
      |> combine_errors
    in
    let e = List.fold_left (fun n acc -> Ap (0, n, acc)) (Top cons) fs in
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
    | Snoc (_, ((_, (_, PCtor _), _) as c))
    | Snoc (_, ((_, (_, PConst _), _) as c)) -> Some c
    | Snoc (cs, _) -> find_split cs
  in
  let rec done_ ctx target constrs wb body =
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
      | Ast.Ap (b, l, r) -> (loc, Ast.Ap (b, rename l, rename r))
      | Ast.Match (sc, bs) ->
        let bs =
          List.map
            (fun (p, wb, b) -> (p, Base.Option.map ~f:rename wb, rename b))
            bs
        in
        (loc, Ast.Match (rename sc, bs))
      | Ast.If (c, t, f) -> (loc, Ast.If (rename c, rename t, rename f))
      | Ast.Lam (p, b) -> (loc, Ast.Lam (p, rename b))
      | Ast.Pi (b, l, r) -> (loc, Ast.Pi (b, rename l, rename r))
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
    | Lin ->
      (*TODO: figure out what to do with the wb *)
      check ctx body target
    | Snoc (cs, (_, (_, PWild), _)) -> done_ ctx target cs wb body
    | Snoc (cs, (new_, (_, PVar prev), _)) ->
       (* rename any occurences of the pattern var with the constr var *)
      let rename = rename_expr prev new_ in
      done_ ctx target cs (rename wb) (rename body)
    | _ -> Error.internal "splittable constraint in done_."
  in
  match (prob.clauses, prob.target) with
  | [], _ -> Error.internal "no cases in build_tree."
  | (_, Snoc.Snoc (_, _), _, _) :: _, VPi (_, l, cl) ->
    let n = fresh_scrut_var () in
    let r = cl $$ VLocal (n, ctx.lvl, Snoc.empty) in
    let ctx = bind_var ~id:n ~t:l ctx in
    let* clauses =
      List.map
        (fun (constrs, pats, wb, b) ->
          match pats with
          | Snoc.Lin -> err (Some ctx.loc, "Clause size doesn't match.")
          | Snoc.Snoc (ps, p) -> Some (constrs @> (n, p, l), ps, wb, b))
        prob.clauses
      |> combine_errors
    in
    let@ b = build_tree ctx {clauses; target = r} in
    Lam (n, b)
  | (constrs, Snoc.Lin, c_wb, c_body) :: _, target -> (
    match find_split constrs with
    | None -> done_ ctx target constrs c_wb c_body
    | Some (sc, (loc, p), _) -> (
      let ctx = update_loc loc ctx in
      match p with
      | PCtor (c, _) ->
        let* dcon, _ = lookup_con loc c ctx in
        let clauses_matched_on clauses nm =
          let rec go cs nm acc =
            match cs with
            | [] -> acc
            | (constrs, _, _, _) :: cs -> (
              match Snoc.find_opt (fun (n, _, _) -> n = nm) constrs with
              | None -> go cs nm acc
              | Some (_, (_, PCtor (c, _)), _) -> go cs nm (c :: acc)
              | Some _ -> go cs nm acc)
          in
          go clauses nm []
        in
        (* | S Z ==> | S (pat$1 ~ Nat) *)
        let push_names ctx dcty =
          let arity pi =
            let rec go n = function
              | VPi (i, _, cl) ->
                let n = n + 1 in
                go n (cl $$ VLocal (i, n, Snoc.empty))
              | _ -> n
            in
            go 0 pi
          in
          (* create binding variables over a constructor, using its type sigature *)
          let rec bind_over_pi ctx lvl pi ps acc =
            match (ps, pi) with
            | p :: ps, VPi (n, l, cl) ->
              bind_over_pi (bind_var ~id:p ~t:l ctx) (lvl + 1)
                (cl $$ VLocal (n, lvl, Snoc.empty))
                ps
                (acc @> (p, l))
            | [p], t -> some (bind_var ~id:p ~t ctx, acc @> (p, t))
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
            | Snoc.Snoc (cs, ((n, (loc, p), _) as constr)) when n = sc -> (
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
                else if dc <> c' then
                  None
                else
                  let binds =
                    Snoc.map2
                      (fun (n, t) p -> (n, p, t))
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
                  (fun (c, ps, wb, b) ->
                    let@ c = rewrite_constr ctx pts c d in
                    Some (c, ps, wb, b))
                  prob.clauses
                |> combine_errors
              in
              let* t = build_tree ctx {clauses; target = prob.target} in
              let args =
                Snoc.map (fun (p, _) -> (loc, PVar p)) pts |> Snoc.to_list
              in
              let b = ((loc, PCtor (d, args)), Const (Bool true), nf ctx t) in
              build_cases (b :: c_acc) cs
          in
          let build_default_case ctx missed =
            (* builds a fallback case for any missing constructors. *)
            let clauses =
              List.filter
                (fun (constrs, _, _, _) ->
                  match Snoc.find_opt (fun (sc', _, _) -> sc' = sc) constrs with
                  | Some (_, (_, PWild), _) -> true
                  | Some (_, (_, PVar _), _) -> true
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
              some ((loc, PWild), Const (Bool true), hole)
            | _ ->
              let@ tree =
                build_tree ctx
                  {clauses = List.rev clauses; target = prob.target}
              in
              ((loc, PWild), Const (Bool true), nf ctx tree)
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
            | (constrs, _, _, _) :: cs -> (
              match Snoc.find_opt (fun (n, _, _) -> n = nm) constrs with
              | None -> go cs nm acc
              | Some (_, (_, PConst c), _) -> go cs nm (c :: acc)
              | Some _ -> go cs nm acc)
          in
          go clauses nm []
        in
        let rewrite_constr ctx constr const =
          let rec go ctx cs acc =
            match cs with
            | Snoc.Lin -> some acc
            | Snoc.Snoc (cs, ((n, (loc, p), _) as constr)) when n = sc -> (
              match p with
              | PTypeLit _ | PCtor _ -> Error.internal "splittable in splitted"
              | PConst c' ->
                if not (equal_const const c') then
                  err
                    ( Some loc,
                      Printf.sprintf "Expected %s, but got %s"
                        (show_const const) (show_const c') )
                else if not (const %= c') then
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
                  (fun (constr, ps, wb, b) ->
                    let@ constr = rewrite_constr ctx constr const in
                    Some (constr, ps, wb, b))
                  prob.clauses
                |> combine_errors
              in
              let* t = build_tree ctx {clauses; target = prob.target} in
              let c = ((loc, PConst const), Const (Bool true), nf ctx t) in
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
                (fun (constrs, _, _, _) ->
                  match Snoc.find_opt (fun (sc', _, _) -> sc' = sc) constrs with
                  | Some (_, (_, PWild), _) | Some (_, (_, PVar _), _) -> true
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
              ((loc, PWild), Const (Bool true), nf ctx tree)
          in
          let* bcs = build_cases [] hit in
          let@ def = build_default_case ctx in
          bcs @ [def]
        in
        let t = Match (sctm, cases) in
        (* attempt to reduce any lambda/inlined function application *)
        eval ctx.env t |> quote ctx.lvl
      | _ -> Error.internal "unsplittable pattern from find_split."))
  | _ -> Error.todo "bing"

let rec check_definition (ctx : ctx) (loc, (i, args, wb, b, locals)) :
    (located_definition list * ctx) result =
  let* locals, ctx' = check_locals ctx locals in
  let clause = (Snoc.empty, Snoc.of_rev_list args, unoption_wb loc wb, b) in
  let* inline, target = get_target i ctx' in
  let@ b = build_tree ctx' {clauses = [clause]; target} in
  let t = force target in
  let d = (loc, (quote ctx'.lvl t, i, b)) in
  let ctx = define_func ~id:i ~t ~v:(inline, b) ctx in
  (d :: locals, ctx)

and check_flpm ctx ((loc, (i, args, wb, b, locals)) as def) ds =
  let* remaining, matched =
    let rec go failed_acc acc = function
      | [] -> Some (failed_acc, acc)
      | ((_, (i', args', _, _, _)) as d) :: ds
        when i' = i && List.length args = List.length args' ->
        let* r = List.map2 (equal_pat ctx) args args' |> combine_errors in
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
          (fun (_, (_, args, wb, ((loc, _) as b), _)) ->
            (Snoc.empty, Snoc.of_rev_list args, unoption_wb loc wb, b))
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
        go [] ctx' @@ List.map (fun (_, (_, _, _, _, locals)) -> locals) ms'
      in
      let def = (Snoc.empty, Snoc.of_rev_list args, unoption_wb loc wb, b) in
      let* inline, target = get_target i ctx' in
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
      | (loc, (i, args, wb, b, locals)) :: ds -> (
        let args = List.map (to_pattern ctx) args |> combine_errors in
        match args with
        | None -> go ctx (None :: acc) ds
        | Some args -> (
          let d = (loc, (i, args, wb, b, locals)) in
          match check_definition ctx d with
          | Some (d, ctx) -> go ctx (Some d :: acc) ds
          | None -> go ctx (None :: acc) ds))
    in
    let r, ctx =
      List.filter_map
        (function
          | loc, Ast.Def (i, args, wb, b, locals) ->
            Some (loc, (i, args, wb, b, locals))
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

and unoption_wb loc = function
  | None -> (loc, Ast.Const (Bool true))
  | Some wb -> wb

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
            | Pi (n, _, r) -> go r (acc @> n)
            | _ -> acc
          in
          go pi Snoc.empty
        in
        (* ( × ) a b ⇒ ( × ) 1 0 *)
        let ap, _ =
          Snoc.fold_left
            (fun (acc, n) i -> (Ap (0, acc, Local (i, n)), n + 1))
            (Top cons, 0) id_stack
        in
        (* ( × ) 1 0 ⇒ λ λ. ( × ) 1 0 *)
        let v = Snoc.fold_right (fun i acc -> Lam (i, acc)) id_stack ap in
        Log.dbg None (Format.asprintf "Turned pi into %a@." pp_tm v);
        v
      in
      let params_to_pi params =
        let ret, _ =
          List.fold_left
            (fun (ap, n) (i, _) -> (Ap (0, ap, Local (i, n)), n + 1))
            (TypeLit (PUni 0), 0) params
        in
        List.fold_right (fun (i, t) acc -> Pi (i, t, acc)) params ret
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
                (fun (_, n) acc -> Pi (fresh_bind_var (), n, acc))
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
          | loc, Ast.Def (i, args, wb, b, locals) ->
            Some (loc, (i, args, wb, b, locals))
          | _ -> None)
        defs
    in
    let* defs =
      List.map
        (fun (loc, (i, args, wb, b, locals)) ->
          let@ args = List.map (to_pattern ctx) args |> combine_errors in
          (loc, (i, args, wb, b, locals)))
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
