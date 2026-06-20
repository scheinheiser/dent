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
  | Lam (p, t) -> VLam (p, (env, t))
  | Pi (n, l, r) -> VPi (n, eval env l, (env, r))
  | Ap (_, l, r) -> v_ap (eval env l) (eval env r)
  | Mv m -> v_meta m
  | IMv (m, bds) -> v_ap_bds env bds (v_meta m)
  | Match (c, bs) ->
    let c = eval env c in
    VMatch (c, env, bs)
  | Let (_, _, v, n) -> eval (env @> eval env v) n

(* β-reduction. *)
and ( $$ ) ((env, t) : closure) (v : val_) : val_ = eval (env @> v) t

and v_ap l r =
  match l with
  | VLam (_, t) -> t $$ r
  | VMeta (m, sp) -> VMeta (m, sp @> r)
  | VLocal (i, lvl, sp) -> VLocal (i, lvl, sp @> r)
  | VTop (i, sp) -> VTop (i, sp @> r)
  | _ -> Error.internal "Called `v_ap` on non-function."

(* unroll a spine *)
and v_ap_sp spine v =
  match spine with
  | Snoc.Lin -> v
  | Snoc.Snoc (spvs, s) -> v_ap (v_ap_sp spvs v) s

and v_meta m =
  match IM.find m !mctx with
  | Solved v -> v
  | Unsolved -> VMeta (m, Snoc.empty)

and v_ap_bds env bds m =
  match (env, bds) with
  | Lin, Lin -> m
  | Snoc (env, e), Snoc (bds, bd) -> (
    match bd with
    | B -> v_ap (v_ap_bds env bds m) e
    | D -> v_ap_bds env bds m)
  | _ ->
    Log.dbg None
      (Format.asprintf "env, bds := %d, %d@." (Snoc.length env)
         (Snoc.length bds));
    Error.internal "Mismatched env/bds list."

(* reduce a metavariable if possible *)
let force = function
  | VMeta (m, sp) as flex -> (
    match lookup_mv m with
    | Solved v ->
      Log.dbg None
        (Format.asprintf "pulled solution from mctx := %d ⇒ %a@." m pp_val v);
      let v = v_ap_sp sp v in
      Log.dbg None
        (Format.asprintf "evaluated solution from mctx := %a@." pp_val v);
      v
    | Unsolved -> flex)
  | v -> v
