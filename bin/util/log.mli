type t =
    | Debug of src option * string
    | Info of string
    | Warn of (Location.t option * string)
    | Error of (Location.t option * string)

and src = (string * string * int * int * int)

(* turns the compiler debug values into a value of type src *)
val comp_to_src : string -> (string * int * int * int) -> src

(* formats an optional src and message into a debug message *)
val fmt_debug : src option -> string -> string

(* formats a given message into an info message *)
val fmt_info : string -> string

(* formats an optional location and message into a warning message *)
val fmt_warn : Location.t option -> string -> string

(* formats an optional location and message into an error message *)
val fmt_error : Location.t option -> string -> string

(* takes a given message type, formats it and prints it to the console. *)
val log : t -> unit

(* helpers to more conveniently log messages to the console *)
val dbg : src option -> string -> unit
val info : string -> unit
val warn : (Location.t option * string) -> unit
val err : (Location.t option * string) -> unit
