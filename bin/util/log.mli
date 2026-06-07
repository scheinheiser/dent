(* severity of the message *)
type t =
  | Debug of (src option * string)
  | Info of string
  | Warn of (Location.t option * string)
  | Error of (Location.t option * string)

(* location in the compiler's source code *)
and src = string * string * int * int * int

(* turns the compiler debug values into a value of type src *)
val comp_to_src : string -> string * int * int * int -> src

(* formats a logged message *)
val fmt_debug : src option -> string -> string
val fmt_info : string -> string
val fmt_warn : Location.t option -> string -> string
val fmt_error : Location.t option -> string -> string

(* format and print the logged message *)
val log : t -> unit

(* convenience logger functions *)
val dbg : src option -> string -> unit
val info : string -> unit
val warn : Location.t option * string -> unit
val err : Location.t option * string -> unit
