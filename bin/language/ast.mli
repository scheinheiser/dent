open Util
open Primitive

(* type definitions *)
type located_expr = Location.t * expr

and expr =
  | Tuple of located_expr * located_expr
  | Ap of binder * located_expr * located_expr
  (* we give each function a binder to distinguish between user-defined
     functions and builtins later on *)
  | Let of
      located_expr
      * located_expr option
      * located_expr
      * located_expr (* let p₁ ... pₙ : <optional_ty> = e₁ in e₂ *)
  | Match of
      located_expr * (located_expr * located_expr option * located_expr) list
  | If of located_expr * located_expr * located_expr
  | Lam of located_expr * located_expr
  | Const of const
  | Var of ident
  | TypeLit of prim
  | Pi of bind * located_expr * located_expr
  | RCons of
      string * (string * located_expr) list (* cons { x₁ = y₁; ...; xₙ = yₙ } *)
  | RUpdate of string * (update_type * string * located_expr) list
    (* { x where y₁ = z₁; ...; yₙ = zₙ } *)
  | Hole (* _ *)
  | Impossible (* ! - an impossible pattern *)
  | Annot of located_expr * located_expr (* e ~ t *)
  | As of string * located_expr (* x@y *)

and bind = string * icit (* identifier, is implicit? *)

and update_type =
  | Assign (* { x where y₁ := z₁ } *)
  | Apply (* { x where y₁ =@ z₁ } - z₁ is a function. *)

type located_ty_decl = Location.t * ty_decl
and ty_decl = string * tdecl_type

and tdecl_type =
  | Alias of located_expr
  | Variant of located_expr * (string * located_expr) list
  | Record of
      string * (string * located_expr) list * (string * located_expr) list

type located_definition = Location.t * definition

and definition =
  | Dec of bool * string * located_expr
  | Def of
      string
      * located_expr list
      * located_expr option
      * located_expr
      * with_block
(* identifer, args, optional when-block, body, optional with-block *)

and with_block = located_definition list

type top_lvl =
  | TDef of located_definition
  | TTyDecl of located_ty_decl
  | TImport of located_import

type program =
  string * located_import list * located_ty_decl list * located_definition list

val pp_expr : Format.formatter -> located_expr -> unit
val pp_definition : Format.formatter -> located_definition -> unit
val pp_program : Format.formatter -> program -> unit
