open Util
open Core

let ( @> ) = Snoc.( @> )

(* term → val *)
let rec eval (env : env) (tm : tm) : val_ =
  match tm with
  | Local (n, i) ->
    Log.dbg None
      (Format.asprintf "@[<v>indexing %s with %d into env.@,env ↦ [ %s ]@]" n i
         (pp_sp pp_val env));
    Snoc.nth env i
  | TypeLit p -> VTypeLit p
  | Const c -> VConst c
  | Top i -> VTop (i, Snoc.empty)
  | Tuple (l, r) -> VTuple (eval env l, eval env r)
  | Lam (p, icit, t) -> VLam (p, icit, (env, t))
  | Pi (n, icit, l, r) -> VPi (n, icit, eval env l, (env, r))
  | Ap (_, l, r, icit) -> v_ap (eval env l) (eval env r) icit
  | Mv m -> v_meta m
  | IMv (m, bds) -> v_ap_bds env bds (v_meta m)
  | Match (c, bs) ->
    let c = eval env c in
    VMatch (c, env, bs)
  | Let (_, _, v, n) -> eval (env @> eval env v) n

(* β-reduction. *)
and ( $$ ) ((env, t) : closure) (v : val_) : val_ = eval (env @> v) t

and v_ap l r icit =
  match l with
  | VLam (_, _, t) -> t $$ r
  | VMeta (m, sp) -> VMeta (m, sp @> (r, icit))
  | VLocal (i, lvl, sp) -> VLocal (i, lvl, sp @> (r, icit))
  | VTop (i, sp) -> VTop (i, sp @> (r, icit))
  | _ -> Error.internal "Called `v_ap` on non-function."

(* unroll a spine *)
and v_ap_sp spine v =
  match spine with
  | Snoc.Lin -> v
  | Snoc.Snoc (spvs, (s, i)) -> v_ap (v_ap_sp spvs v) s i

and v_meta m =
  match IM.find m !mctx with
  | Solved v -> v
  | Unsolved -> VMeta (m, Snoc.empty)

and v_ap_bds env bds m =
  match (env, bds) with
  | Lin, Lin -> m
  | Snoc (env, e), Snoc (bds, bd) -> (
    match bd with
    | B -> v_ap (v_ap_bds env bds m) e Exp
    | D -> v_ap_bds env bds m)
  | _ -> Error.internal "Mismatched env/bds list."

(* compute the arity of a function through its type *)
let arity pi =
  let rec go n = function
    | VPi (i, _,  _, cl) ->
      let n = n + 1 in
      go n (cl $$ VLocal (i, n, Snoc.empty))
    | _ -> n
  in
  go 0 pi

(* reduce a metavariable if possible *)
let force = function
  | VMeta (m, sp) as flex -> (
    match lookup_mv m with
    | Solved v -> v_ap_sp sp v
    | Unsolved -> flex)
  | v -> v

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
    let quote_b env (p, b) =
      let rec build_env env (_, p) l =
        match p with
        | PWild | PTypeLit _ | PConst _ | PAbs -> (env, l)
        | PVar i -> (env @> VLocal (i, l, Snoc.empty), l + 1)
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
      let b = eval env b |> quote l in
      (p, b)
    in
    let bs = List.map (quote_b env) bs in
    Match (c, bs)
  | VLam (p, icit, cl) ->
    (*
       increment the level as we move past a binder.
       add a local with the current level to capture the argument.
    *)
    Lam (p, icit, quote (lvl + 1) (cl $$ VLocal (p, lvl, Snoc.empty)))
  | VPi (n, icit, l, cl) ->
    let l = quote lvl l in
    let r = quote (lvl + 1) (cl $$ VLocal (n, lvl, Snoc.empty)) in
    Pi (n, icit, l, r)
  | VMeta (m, sp) -> quote_sp lvl (Mv m) sp
  | VLocal (i, l, sp) -> quote_sp lvl (Local (i, to_ix lvl l)) sp

(* unroll a flex/rigid into a set of applications *)
and quote_sp (lvl : lvl) (v : tm) (sp : spine) : tm =
  match sp with
  | Snoc.Lin -> v
  | Snoc.Snoc (sp, (s, icit)) -> Ap (0, quote_sp lvl v sp, quote lvl s, icit)
