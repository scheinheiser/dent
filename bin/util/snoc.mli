(* a reversed list. *)
type 'a t =
  | Lin
  | Snoc of 'a t * 'a

val empty : 'a t
val singleton : 'a -> 'a t
val length : 'a t -> int
val hd : 'a t -> 'a
val nth : 'a t -> int -> 'a

(* append and prepend a value to the list respectively *)
val ( @> ) : 'a t -> 'a -> 'a t
val ( <@ ) : 'a t -> 'a t -> 'a t
val flatten : 'a t t -> 'a t
val reverse : 'a t -> 'a t
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list

(* snoc list transformations *)
val map : ('a -> 'b) -> 'a t -> 'b t
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
val find_opt : ('a -> bool) -> 'a t -> 'a option

(* find_map that carries an index for each element in list *)
val find_mapi : (int -> 'a -> 'b option) -> 'a t -> 'b option

(* evaluate a list of optional values *)
val combine_errors : 'a option t -> 'a t option
