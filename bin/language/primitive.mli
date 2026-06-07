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

type located_pattern = Location.t * pattern

and pattern =
  | PWild (* _ *)
  | PConst of const
  | PTypeLit of prim
  | PVar of string
  | PCtor of string * located_pattern list
  | PTuple of located_pattern * located_pattern

type located_import = Location.t * import
and import = ident * import_cond option

and import_cond =
  | CWith of ident list
  | CWithout of ident list

(* const *)
val const_equality : const -> const -> bool
val ( %= ) : const -> const -> bool

(* prims *)
val prim_equality : prim -> prim -> bool
val ( #= ) : prim -> prim -> bool
val show_prim : prim -> string

(* idents *)
val get_str : ident -> string

(* pretty printing *)
val pp_ident : Format.formatter -> ident -> unit
val pp_prim : Format.formatter -> prim -> unit
val pp_const : Format.formatter -> const -> unit
val pp_pattern : Format.formatter -> located_pattern -> unit
val pp_import_cond : Format.formatter -> import_cond -> unit
val pp_import : Format.formatter -> located_import -> unit
