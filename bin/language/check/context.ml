open Util
open Core

let ( @> ) = Snoc.( @> )

let err e =
  Log.err e;
  None

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
  | Def of (bool * tm)
  | RCon of string * (string * tm) list
  | DCon of (string * tm)
    (* type constructor name, the function that constructs the value. *)
  | TCon of string list (* a list of all of the data constructors *)
  | Alias of tm
  | Axiom of bool

let empty_ctx () =
  {
    loc = Location.dummy_loc;
    env = Snoc.empty;
    top = SM.empty;
    tys = Snoc.empty;
    lvl = 0;
    bds = Snoc.empty;
  }

(* helper functions for operations on ctx *)
let flush_locals ctx =
  {ctx with env = Snoc.empty; tys = Snoc.empty; lvl = 0; bds = Snoc.empty}

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

let bind_func ~(id : string) ~(t : val_) ~(inline: bool) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = Axiom inline} ctx.top}

let define_func ~(id : string) ~(v : bool * tm) ~(t : val_) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = Def v} ctx.top}

let define_dcon ~(id : string) ~(t : val_) ~(v : string * tm) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = DCon v} ctx.top}

let define_tcon ~(id : string) ~(t : val_) ~(constrs : string list) (ctx : ctx)
    =
  {ctx with top = SM.add id {ty = t; def = TCon constrs} ctx.top}

let define_rcon ~(id : string) ~(t : val_) ~(tcon : string)
    ~(fields : (string * tm) list) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = RCon (tcon, fields)} ctx.top}

let define_alias ~(id : string) ~(t : val_) ~(ty : tm) (ctx : ctx) =
  {ctx with top = SM.add id {ty = t; def = Alias ty} ctx.top}

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
