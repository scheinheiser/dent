type t = { filename : string; start_line : int; end_line : int; start_col : int; end_col : int }

(* dummy location, where values are initialised to defaults. *)
val dummy_loc : t

(* pretty print location *)
val pp_location : Format.formatter -> t -> unit

(* make a location out of a lexing buffer *)
val of_lexbuf : Sedlexing.lexbuf -> t

(* combine two locations *)
val combine : t -> t -> t
