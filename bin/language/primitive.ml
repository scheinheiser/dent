open Util

(* Type definitions *)
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
  | PUni of int (* α ~ U n *)

type icit =
  | Imp
  | Exp

type located_import = Location.t * import
and import = ident * import_cond option

and import_cond =
  | CWith of ident list
  | CWithout of ident list

(* utils *)
let rec const_equality l r =
  match (l, r) with
  | Int l, Int r -> l = r
  | Float l, Float r -> l = r
  | String l, String r -> l = r
  | Char l, Char r -> l = r
  | Bool l, Bool r -> l = r
  | Unit, Unit -> true
  | _ -> false

and ( %= ) l r = const_equality l r

let rec prim_equality l r =
  match (l, r) with
  | PInt, PInt
  | PFloat, PFloat
  | PString, PString
  | PChar, PChar
  | PBool, PBool
  | PUnit, PUnit -> true
  | PUni n, PUni n' -> n <= n'
  | _ -> false

and ( #= ) l r = prim_equality l r

let show_prim = function
  | PInt -> "Int"
  | PFloat -> "Float"
  | PString -> "String"
  | PChar -> "Char"
  | PBool -> "Bool"
  | PUnit -> "Unit"
  | PUni n -> Printf.sprintf "U%d" n

(* idents *)
let get_str = function
  | Ident i | Udc i -> i
  | AccessIdent (base, is) -> Printf.sprintf "%s.%s" base (String.concat "." is)

(* pretty printing *)
let pp_ident out (i : ident) =
  match i with
  | Ident i | Udc i -> Format.fprintf out "%s" i
  | AccessIdent (i, is) -> Format.fprintf out "%s.%s" i (String.concat "." is)

let pp_prim out (t : prim) = Format.fprintf out "%s" (show_prim t)

let pp_const out (c : const) =
  match c with
  | Int i -> Format.fprintf out "%d" i
  | Float f -> Format.fprintf out "%.3f" f
  | String s -> Format.fprintf out "\"%s\"" s
  | Char c -> Format.fprintf out "'%s'" (Char.escaped c)
  | Bool b -> Format.fprintf out "%b" b
  | Unit -> Format.fprintf out "()"

let pp_import_cond out (cond : import_cond) =
  match cond with
  | CWith includes ->
    Format.fprintf out "with (@[<hov>%a@])"
      Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out " ") pp_ident)
      includes
  | CWithout excludes ->
    Format.fprintf out "without (@[<hov>%a@])"
      Format.(pp_print_list ~pp_sep:(fun out () -> fprintf out " ") pp_ident)
      excludes

let pp_import out ((_, (mod_name, cond)) : located_import) =
  Format.fprintf out "(import %a @[<hov>%a@])" pp_ident mod_name
    Format.(
      pp_print_option ~none:(fun out () -> fprintf out "()") pp_import_cond)
    cond
