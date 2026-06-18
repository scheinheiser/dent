open Util

type binder = int

type ident =
  | Ident of string
  | AccessIdent of string * string list
  | Udc of string (* user defined costructor *)

type const =
  | Int of int
  | Float of float
  | String of string
  | Char of char
  | Bool of bool
  | Unit

type prim =
  | PInt
  | PFloat
  | PString
  | PChar
  | PBool
  | PUnit
  | PUni of int

type icit =
  | Imp
  | Exp

type located_import = Location.t * import
and import = ident * import_cond option

and import_cond =
  | CWith of ident list
  | CWithout of ident list

(* const *)
val equal_const : const -> const -> bool
val ( %= ) : const -> const -> bool
val show_const : const -> string (* shows the name of the constant *)

(* prims *)
val equal_prim : prim -> prim -> bool
val ( #= ) : prim -> prim -> bool
val show_prim : prim -> string

(* idents *)
val get_str : ident -> string

(* pretty printing *)
val pp_ident : Format.formatter -> ident -> unit
val pp_prim : Format.formatter -> prim -> unit
val pp_const : Format.formatter -> const -> unit
val pp_import_cond : Format.formatter -> import_cond -> unit
val pp_import : Format.formatter -> located_import -> unit
