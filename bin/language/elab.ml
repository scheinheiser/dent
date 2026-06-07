(* based on https://github.com/AndrasKovacs/elaboration-zoo *)
open Util
open Primitive

let flip = Fun.flip
let ( @> ) = Snoc.( @> )
let singleton = Snoc.singleton
let replicate n v = List.init n (fun _ -> v)

let fresh_i =
  let i = ref (-1) in
  fun () ->
    incr i;
    !i

type ix = int
type lvl = int
type mv = int

module IM = Map.Make (Int)
module SM = Map.Make (String)

(* bound or defined variables *)
type bd =
  | B
  | D

(*NOTE: removed location tracking, might be useful to keep it *)
(* core syntax, tms *)
type tm =
  | Local of string * ix (* local variable as de bruijn index *)
  | Top of string (* reference to a top level function *)
  | Ap of binder * tm * tm
  | Mv of mv
  | IMv of mv * bd Snoc.t (* generated mv *)
  | Tuple of tm * tm
  | Let of string * tm * tm * tm (* let p₁ ... pₙ : type = e₁ in e₂ *)
  | Match of tm * (located_pattern * tm * tm) list
    (* match cond to | p₁ when x₁ => y₁ ... | pₙ when xₙ => yₙ*)
  | Lam of string * tm
  | Const of const
  | TypeLit of prim
  | Pi of string * tm * tm (* (α : β) -> γ *)

(* values for NbE *)
and val_ =
  | VLam of string * closure
  | VTop of string * spine
  | VLocal of string * lvl * spine
  | VMeta of mv * spine
  | VTuple of val_ * val_
  | VMatch of val_ * env * (located_pattern * tm * tm) list
  | VPi of string * val_ * closure
  | VTypeLit of prim
  | VConst of const

and env = val_ Snoc.t

(* list of variables that a mv or local is applied to *)
and spine = val_ Snoc.t

and mv_entry =
  | Solved of val_
  | Unsolved

and closure = env * tm

(* top level extras *)
type located_ty_decl = Location.t * ty_decl
and ty_decl = string * tdecl_type

and tdecl_type =
  | Alias of tm
  | Variant of tm * (string * tm) list
  | Record of string * tm * (string * tm) list

type located_definition = Location.t * definition
and definition = tm * string * tm (* type, identifer, body *)

type program =
  string * located_import list * located_ty_decl list * located_definition list

let mctx : mv_entry IM.t ref = ref IM.empty

(* should never fail *)
let lookup_mv (m : mv) : mv_entry = IM.find m !mctx

let gen_mv bds : tm =
  let mv = fresh_i () in
  mctx := IM.add mv Unsolved !mctx;
  IMv (mv, bds)

(* pretty printing *)
let rec pp_tm out (tm : tm) =
  match tm with
  | Local (i, _) | Top i -> Format.fprintf out "%s" i
  | Const c -> pp_const out c
  | TypeLit p -> pp_prim out p
  | Ap (_, f, arg) ->
    Format.fprintf out "(@[<hov>%a@ %@ %a@])" pp_tm f pp_tm arg
  | Tuple (l, r) -> Format.fprintf out "(%a, %a)" pp_tm l pp_tm r
  | Let (p, ty, v, n) ->
    Format.fprintf out "@[<v 2>let %s : %a =@,%a@]@,in@,%a" p pp_tm ty pp_tm v
      pp_tm n
  | Lam (arg, body) ->
    Format.fprintf out "λ@[<v 2> %s. {@,%a@]@,}" arg pp_tm body
  | Match (c, bs) ->
    let pp_branch out (p, wb, b) =
      Format.fprintf out "(wh@[<v>en %a)@,(%a) ⇒ %a@]" pp_tm wb pp_pattern p
        pp_tm b
    in
    Format.fprintf out "ma@[<v>tch (%a)@,%a@]" pp_tm c
      Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
      bs
  | Pi (n, l, r) ->
    Format.fprintf out "@[<v>(%s : %a) -> %a@]" n pp_tm l pp_tm r
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
  | VTop (i, sp) -> Format.fprintf out "%s (%s)" i (pp_sp pp_val sp)
  | VLam (p, cl) -> Format.fprintf out "λ@[<v> %s. {@,%a@]@,}" p pp_closure cl
  | VTuple (l, r) -> Format.fprintf out "(%a, %a)" pp_val l pp_val r
  | VMatch (c, _, bs) ->
    let pp_branch out (p, wb, b) =
      Format.fprintf out "(wh@[<v>en %a)@,(%a) ⇒ %a@]" pp_tm wb pp_pattern p
        pp_tm b
    in
    Format.fprintf out "ma@[<v>tch (%a)@,%a@]" pp_val c
      Format.(pp_print_list ~pp_sep:pp_print_cut pp_branch)
      bs
  | VPi (n, l, cl) ->
    Format.fprintf out "(%s : %a) -> %a" n pp_val l pp_closure cl
  | VLocal (i, _, sp) -> Format.fprintf out "%s (%s)" i (pp_sp pp_val sp)
  | VMeta (m, sp) -> Format.fprintf out "?meta%d (%s)" m (pp_sp pp_val sp)

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

(* pretty much β-reduction. *)
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
  | _ -> Error.internal "Mismatched env/bds list."

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
        | PWild | PTypeLit _ | PConst _ -> (env, l)
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
          (args, l + Snoc.length args)
        (* adding arg length is kinda sus *)
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

type ctx = {
  loc : Location.t; (* for more convenient error reporting *)
  env : env;
  top : top_entry SM.t;
  tys : (string * val_) Snoc.t;
  lvl : lvl;
  bds : bd Snoc.t;
}

(*TODO: don't use a record here *)
and top_entry = {
  ty : val_;
  def : def;
}

and def =
  | Def of tm
  | RCon of string * (string * tm) list
  | DCon of (string * tm)
    (* type constructor name, the function that constructs the value. *)
  | TCon of string list (* a list of all of the data constructors *)
  | Axiom

let empty_ctx () =
  {
    loc = Location.dummy_loc;
    env = Snoc.empty;
    top = SM.empty;
    tys = Snoc.empty;
    lvl = 0;
    bds = Snoc.empty;
  }

let flush_locals ctx =
  {ctx with env = Snoc.empty; tys = Snoc.empty; lvl = 0; bds = Snoc.empty}

(* helper functions for operations on ctx *)
let update_loc (loc : Location.t) (ctx : ctx) = {ctx with loc}

let bind_var ~(id : string) ~(t : val_) (ctx : ctx) =
  {
    ctx with
    env = ctx.env @> VLocal (id, ctx.lvl, Snoc.empty);
    tys = ctx.tys @> (id, t);
    lvl = ctx.lvl + 1;
    bds = ctx.bds @> B;
  }

let define_var ~(id : string) ~(v : val_) ~(t : val_) (ctx : ctx) =
  {
    ctx with
    env = ctx.env @> v;
    tys = ctx.tys @> (id, t);
    lvl = ctx.lvl + 1;
    bds = ctx.bds @> D;
  }

let bind_func ~(id : string) ~(t : val_) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = Axiom} ctx.top}

let define_func ~(id : string) ~(v : tm) ~(t : val_) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = Def v} ctx.top}

let define_dcon ~(id : string) ~(t : val_) ~(v : string * tm) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = DCon v} ctx.top}

let define_tcon ~(id : string) ~(t : val_) ~(constrs : string list) (ctx : ctx)
    =
  {ctx with top = SM.add id {ty = t; def = TCon constrs} ctx.top}

let define_rcon ~(id : string) ~(t : val_) ~(tcon : string)
    ~(fields : (string * tm) list) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = RCon (tcon, fields)} ctx.top}

let lookup_local (i : string) (ctx : ctx) : (int * val_) option =
  let r =
    Snoc.find_mapi (fun n (x, t) -> if x = i then Some (n, t) else None) ctx.tys
  in
  match r with
  | None -> err (Some ctx.loc, Printf.sprintf "Undefined identifier - '%s'." i)
  | Some v -> Some v

let lookup_top (i : string) (ctx : ctx) : (def * val_) option =
  match SM.find_opt i ctx.top with
  | Some top -> Some (top.def, top.ty)
  | None -> None

let lookup_tcon (i : string) (ctx : ctx) : (string list * val_) option =
  match lookup_top i ctx with
  | Some (TCon constrs, ty) -> Some (constrs, ty)
  | _ ->
    err (Some ctx.loc, Printf.sprintf "Undefined type constructor - '%s'." i)

let lookup_dcon (i : string) (ctx : ctx) : ((string * tm) * val_) option =
  match lookup_top i ctx with
  | Some (DCon d, ty) -> Some (d, ty)
  | _ ->
    err (Some ctx.loc, Printf.sprintf "Undefined data constructor - '%s'." i)

let lookup_rcon (i : string) (ctx : ctx) :
    (string * (string * tm) list * val_) option =
  match lookup_top i ctx with
  | Some (RCon (con, r), ty) -> Some (con, r, ty)
  | _ ->
    err (Some ctx.loc, Printf.sprintf "Undefined record constructor - '%s'." i)

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
      (fun (_, _, b) (_, _, b') ->
        let b = eval env b in
        let b' = eval env' b' in
        unify ctx b b')
      bs bs'
    |> combine_errors_unit
  | VLocal (_, ri, sp), VLocal (_, ri', sp') when ri = ri' ->
    unify_sp ctx sp sp'
  | VTop (i, sp), VTop (i', sp') when i = i' -> unify_sp ctx sp sp'
  | VTop (i, sp), t | t, VTop (i, sp) -> (
    match lookup_top i ctx with
    | None -> err (Some ctx.loc, Printf.sprintf "Undefined identifier - '%s'." i)
    | Some (Def b, _) ->
      let b = eval Snoc.empty b |> v_ap_sp sp in
      unify ctx b t
    | Some (DCon _, t') | Some (TCon _, t') -> unify ctx t' t
    | Some (RCon _, _) -> Error.todo ""
    | Some (Axiom, _) ->
      err (Some ctx.loc, Printf.sprintf "The function '%s' has no definition." i)
    )
  | VMeta (mv, sp), VMeta (mv', sp') when mv = mv' -> unify_sp ctx sp sp'
  | VMeta (mv, sp), t | t, VMeta (mv, sp) -> solve ctx.loc ctx.lvl mv sp t
  | l, r -> uni_err (Some ctx.loc) pp_val l r

and uni_err loc pp_func ex got =
  err
    ( loc,
      Format.asprintf
        "Va@[<v 4>lue unification failed:@,Expected → %a@,Received → %a@,@]"
        pp_func ex pp_func got )

let fresh_pattern_var () : string = "pat$" ^ (fresh_i () |> string_of_int)
let fresh_bind_var () : string = "b$" ^ (fresh_i () |> string_of_int)
let fresh_scrut_var () : string = "c_id$" ^ (fresh_i () |> string_of_int)

let replace_pattern ((_, p) : located_pattern)
    ((loc, _) as b : Ast.located_expr) : string * Ast.located_expr =
  match p with
  | PVar i -> (i, b)
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
    let t = ((loc, PConst (Bool true)), None, t) in
    let f = ((loc, PConst (Bool false)), None, f) in
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
    let cs =
      List.map
        (fun (p, wb, ((loc, _) as b)) ->
          let wb =
            match wb with
            | None -> (loc, Ast.Const (Bool true))
            | Some wb -> wb
          in
          (singleton (c_id, p, t), Snoc.empty, wb, b))
        bs
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
      (*TODO: handle parameterised records, i.e. MyRec α β *)
      (e, VTop (tcon, Snoc.empty))
  | Ast.RUpdate (base, fs) ->
    let lookup_ri id ctx =
      let* cons, t = lookup_tcon id ctx in
      let@ cons, fs, _ = lookup_rcon (List.hd cons) ctx in
      (* the only constructor in the *)
      (cons, fs, t)
    in
    let* n, t = lookup_local base ctx in
    let* ri = get_record_id t in
    let* cons, ex_fs, ret = lookup_ri ri ctx in
    let@ fs =
      List.map
        (fun (ex_i, ex_t) ->
          let ex_t = eval Snoc.empty ex_t in
          Log.dbg None (Format.asprintf "ex_t := %a@." pp_val ex_t);
          match List.find_opt (fun (_, i, _) -> i = ex_i) fs with
          | None ->
            let i = base ^ "." ^ ex_i in
            some @@ Local (i, n)
          | Some (Ast.Assign, f, e) ->
            Log.dbg None (Format.asprintf "assign: %s := %a@." f Ast.pp_expr e);
            check ctx e ex_t
          | Some (Ast.Apply, _, ((loc, _) as f)) ->
            (* apply the function to the field and check that it's the right type. *)
            let field = (loc, Ast.Var (AccessIdent (base, [ex_i]))) in
            let v = (loc, Ast.Ap (0, f, field)) in
            check ctx v ex_t)
        ex_fs
      |> combine_errors
    in
    let e = List.fold_left (fun n acc -> Ap (0, n, acc)) (Top cons) fs in
    (e, ret)
  | e -> Error.todo (Format.asprintf "finish infer - %a" Ast.pp_expr (loc, e))

and infer_universe loc = function
  | VTypeLit (PUni n) -> Some n
  | VTypeLit _ | VMeta _ -> Some 0
  | VTuple (l, r) ->
    let* n = infer_universe loc l in
    let@ n' = infer_universe loc r in
    Int.max n n'
  | v -> err (Some loc, Format.asprintf "Expected a Type, but got %a." pp_val v)

and is_type (ctx : ctx) ((loc, _) as e : Ast.located_expr) : (tm * int) result =
  let* t, tty = infer ctx e in
  let@ n = infer_universe loc tty in
  (t, n)

and build_tree (ctx : ctx) (prob : problem) : tm result =
  let collect_dcons ctx tcon =
    let@ dcons, _ = lookup_tcon tcon ctx in
    dcons
  in
  let rec find_split cs =
    let open Snoc in
    match cs with
    | Lin -> None
    | Snoc (_, ((_, (_, PCtor _), _) as c)) -> Some c
    | Snoc (cs, _) -> find_split cs
    (*TODO: split on literals, types (?) *)
  in
  let rec done_ ctx target constrs wb body =
    let open Snoc in
    match constrs with
    | Lin ->
      (*TODO: figure out what to do with the wb *)
      check ctx body target
    | Snoc (cs, (_, (_, PWild), _)) -> done_ ctx target cs wb body
    | Snoc (cs, (new_, (_, PVar prev), _)) ->
      let ctx =
        {
          ctx with
          tys =
            Snoc.map
              (fun (n, ty) -> if n = prev then (new_, ty) else (n, ty))
              ctx.tys;
        }
      in
      done_ ctx target cs wb body
    | _ -> Error.internal "splittable constraint in done_."
  in
  match (prob.clauses, prob.target) with
  | [], _ -> Error.internal "no cases in build_tree."
  | (_, Snoc.Snoc (_, _), _, _) :: _, VPi (n, l, cl) ->
    let r = cl $$ VLocal (n, ctx.lvl, Snoc.empty) in
    let ctx = bind_var ~id:n ~t:l ctx in
    let* clauses =
      List.map
        (fun (constrs, pats, wb, b) ->
          match pats with
          | Snoc.Lin -> err (Some ctx.loc, "Clause size doesn't match.")
          | Snoc.Snoc (ps, p) ->
            Log.dbg None (Format.asprintf "constr %s := %a@." n pp_pattern p);
            Some (constrs @> (n, p, l), ps, wb, b))
        prob.clauses
      |> combine_errors
    in
    let@ b = build_tree ctx {clauses; target = r} in
    Lam (n, b)
  | (constrs, Snoc.Lin, c_wb, c_body) :: _, target -> (
    match find_split constrs with
    | None -> done_ ctx target constrs c_wb c_body
    | Some (sc, (loc, p), scty) -> (
      match p with
      | PCtor (c, args) -> (
        Log.dbg None (Printf.sprintf "constructor := %s\n" c);
        match lookup_dcon c ctx with
        | None ->
          err
            ( Some loc,
              Printf.sprintf
                "Undefined identifier or non-data constructor - '%s'." c )
        | Some ((dcon, _), _) ->
          (* let* _ = unify ctx target dcty in *)
          let clauses_with_sc clauses nm =
            let rec go cs nm acc =
              match cs with
              | [] -> acc
              | (constrs, _, wb, b) :: cs -> (
                match Snoc.find_opt (fun (n, _, _) -> n = nm) constrs with
                | None -> go cs nm acc
                | Some (_, (_, PCtor (c, _)), t) ->
                  go cs nm ((c, t, wb, b) :: acc)
                | Some _ -> Error.internal "not a constructor.")
            in
            go clauses nm []
          in
          (* | S Z ==> | S (pat$1 ~ Nat) *)
          let push_names ctx dcty =
            let rec bind_over_pi ctx lvl pi ps acc =
              match (ps, pi) with
              | (_, p) :: ps, VPi (n, l, cl) ->
                bind_over_pi (bind_var ~id:p ~t:l ctx) (lvl + 1)
                  (cl $$ VLocal (n, lvl, Snoc.empty))
                  ps
                  (acc @> (p, l))
              | [(_, p)], t -> some (bind_var ~id:p ~t ctx, acc @> (p, t))
              | [], _ ->
                some (ctx, acc)
                (* Z ~ Nat; no constructors so we don't need to bind anything. *)
              | _ ->
                err
                  ( Some loc,
                    "Not enough arguments have been applied to the type \
                     constructor." )
            in
            let ps =
              List.map (fun (loc, _) -> (loc, fresh_pattern_var ())) args
            in
            let@ ctx, pts = bind_over_pi ctx ctx.lvl dcty ps Snoc.empty in
            (ctx, pts)
          in
          let* ds = collect_dcons ctx dcon in
          let found, _ =
            let with_sc = clauses_with_sc prob.clauses sc in
            List.partition
              (fun (n, _, _, _) -> List.exists (( = ) n) ds)
              with_sc
          in
          let@ res =
            let rec go (ctx, c_acc) = function
              | [] -> (ctx, c_acc)
              | (_, t, wb, b) :: cs -> (
                match push_names ctx t with
                | None -> go (ctx, None :: c_acc) cs
                | Some (ctx, pts) ->
                  let constrs =
                    Snoc.map2
                      (fun (p, t) arg -> (p, arg, t))
                      pts (Snoc.of_list args)
                  in
                  let clause = (constrs, Snoc.empty, wb, b) in
                  go (ctx, Some clause :: c_acc) cs)
            in
            let ctx, bcs = go (ctx, []) found in
            let* clauses = combine_errors bcs in
            build_tree ctx {clauses; target = scty}
          in
          Lam (sc, res))
      | _ -> Error.internal "unsplittable pattern from find_split."))
  | _ -> Error.todo "bing"

let rec check_definition (ctx : ctx) (loc, (i, args, wb, b, locals)) :
    (located_definition list * ctx) result =
  (* goes through and typechecks each local definition. *)
  let* locals, ctx' =
    match locals with
    | [] -> some ([], ctx)
    | _ ->
      let* ctx =
        let@ ds =
          List.filter_map
            (function
              | _, Ast.Dec (i, sig_) -> Some (i, sig_)
              | _ -> None)
            locals
          |> List.map (fun (i, sig_) ->
              let@ sig_, _ = is_type ctx sig_ in
              (i, sig_))
          |> combine_errors
        in
        List.fold_left
          (fun ctx (i, sig_) -> bind_func ~id:i ~t:(eval ctx.env sig_) ctx)
          ctx ds
      in
      let rec go ctx acc = function
        | [] -> (List.rev acc, ctx)
        | d :: ds -> (
          match check_definition ctx d with
          | Some (d, ctx) -> go ctx (Some d :: acc) ds
          | None -> go ctx (None :: acc) ds)
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
  in
  let wb =
    match wb with
    | None -> (loc, Ast.Const (Bool true))
    | Some wb -> wb
  in
  let clause = (Snoc.empty, Snoc.of_list args, wb, b) in
  let* target =
    match lookup_top i ctx' with
    | None -> Some (eval Snoc.empty @@ gen_mv ctx.bds)
    | Some (Axiom, t') -> Some t'
    | Some (Def _, _) ->
      err
        ( Some loc,
          Printf.sprintf "The function '%s' has already been defined." i )
    | Some _ ->
      (* shouldn't occur unless it's an operator. *)
      err (Some loc, Printf.sprintf "The identifier '%s' is already in use." i)
  in
  let@ b = build_tree ctx' {clauses = [clause]; target} in
  let d = (loc, (quote ctx'.lvl @@ force target, i, b)) in
  (d :: locals, ctx)

let check_program ((n, mods, tdecls, defs) : Ast.program) : program result =
  let ctx = empty_ctx () in
  let* tdecls, ctx =
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
      | (loc, (n, Ast.Alias t)) :: ts -> (
        match is_type ctx t with
        | None -> check_decls ctx (None :: acc) ts
        | Some (v, l) ->
          let a = (loc, (n, Alias v)) in
          check_decls
            (define_func ~id:n ~t:(VTypeLit (PUni l)) ~v ctx)
            (Some a :: acc) ts)
      | (loc, (n, Ast.Variant (sig_, vs))) :: ts -> (
        let sig_ = is_type ctx sig_ in
        match sig_ with
        | None -> check_decls ctx (None :: acc) ts
        | Some (sig_, _) -> (
          (*TODO: scope any type variables in the sig_. *)
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
      | (loc, (n, Ast.Record (cons, sig_'', fs))) :: ts -> (
        (*TODO: prevent duplicate fields *)
        let sig_ = is_type ctx sig_'' in
        match sig_ with
        | None -> check_decls ctx (None :: acc) ts
        | Some (sig_, _) -> (
          let ctx =
            define_tcon ~id:n ~t:(eval Snoc.empty sig_) ~constrs:[cons] ctx
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
              define_rcon ~id:cons ~t:(eval Snoc.empty csig) ~tcon:n ~fields:fs
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
      | (i, t) :: ts ->
        let* t, _ = is_type ctx t in
        let t = eval Snoc.empty t in
        Log.dbg None (Format.asprintf "%s ↦ %a@." i pp_val t);
        go (bind_func ~id:i ~t ctx) ts
    in
    let decs =
      List.filter_map
        (function
          | _, Ast.Dec (i, t) -> Some (i, t)
          | _ -> None)
        defs
    in
    go ctx decs
  in
  let* defs =
    let defs =
      List.filter_map
        (function
          | loc, Ast.Def (i, as_, wb, b, wb') -> Some (loc, (i, as_, wb, b, wb'))
          | _ -> None)
        defs
    in
    let rec go ctx acc = function
      | [] -> acc
      | d :: ds -> (
        match check_definition ctx d with
        | None -> go ctx (None :: acc) ds
        | Some (d, ctx) -> go (flush_locals ctx) (Some d :: acc) ds)
    in
    go ctx [] defs |> combine_errors
  in
  (*TODO: halt further compilation if a function isn't defined (but has a type signature). *)
  match !holes with
  | [] -> some (n, mods, tdecls, List.rev defs |> List.flatten)
  | _ -> err (None, fmt_holes ())
