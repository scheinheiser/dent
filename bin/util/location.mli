type t = { filename : string; start_line : int; end_line : int; start_col : int; end_col : int }

val dummy_loc : t
val pp_location : Format.formatter -> t -> unit
val of_lexbuf : Lexing.lexbuf -> t
val make : string -> int -> int -> int -> int -> t
val combine : t -> t -> t
