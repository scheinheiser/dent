type 'a t =
  | Lin
  | Snoc of ('a t) * 'a

(* the empty snoc list *)
val empty : 'a t

val length : 'a t -> int 
val nth : 'a t -> int -> 'a

(* push a value to the top of the list *)
val append : 'a t -> 'a -> 'a t
val ( @> ) : 'a t -> 'a -> 'a t

(* turn a list into a snoc list *)
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list

(* apply a function to every element of a list *)
val map : ('a -> 'b) -> 'a t -> 'b t

val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc

val find_mapi : (int -> 'a -> 'b option) -> 'a t -> 'b option
