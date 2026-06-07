(* a location in the file. *)
type t = {
  filename : string;
  start_line : int;
  end_line : int;
  start_col : int;
  end_col : int;
}

(* dummy location with default values *)
val dummy_loc : t

(* pretty print location *)
val pp_location : Format.formatter -> t -> unit

(* make a location out of a lexing buffer *)
val of_lexbuf : Sedlexing.lexbuf -> t

(* combine two locations *)
val combine : t -> t -> t
