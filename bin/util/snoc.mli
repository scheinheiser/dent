(* a reversed list. *)
type 'a t =
  | Lin
  | Snoc of 'a t * 'a

(* the empty snoc list *)
val empty : 'a t

(* find the length of a snoc list & index it *)
val length : 'a t -> int
val nth : 'a t -> int -> 'a

(* push a value to the end and beginning of the list respectively *)
val ( @> ) : 'a t -> 'a -> 'a t
val ( <@ ) : 'a t -> 'a t -> 'a t

(* concatenate a list of lists and reverse a list. *)
val flatten : 'a t t -> 'a t
val reverse : 'a t -> 'a t

(* turn a list into a snoc list *)
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list

(* apply a function to every element of a list *)
val map : ('a -> 'b) -> 'a t -> 'b t

(* folding operations *)
val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
val fold_lefti : (int -> 'acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc (* fold with an index *)
val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc

(* find_map that carries an index for each element in list *)
val find_mapi : (int -> 'a -> 'b option) -> 'a t -> 'b option
