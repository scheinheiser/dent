type t = Location.t option * string

exception InternalError of string
exception Todo of string

val todo : string -> 'a
val internal : string -> 'a
val pp_err : Format.formatter -> t -> unit
val pp_warning : Format.formatter -> t -> unit
val format_err : t -> string
val report_err : t -> 'a
