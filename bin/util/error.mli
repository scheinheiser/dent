type t = Location.t option * string

(* used within the compiler's source code for a malformed state and to document things that will be implemented. *)
exception InternalError of string
exception Todo of string

(* convenience functions *)
val todo : string -> 'a
val internal : string -> 'a

(* pretty printers and formatters *)
val pp_err : Format.formatter -> t -> unit
val pp_warning : Format.formatter -> t -> unit
val format_err : t -> string
val report_err : t -> 'a
