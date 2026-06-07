type 'a t =
  | Lin
  | Snoc of 'a t * 'a

let empty = Lin
let singleton v = Snoc (Lin, v)

let length s =
  let rec go s acc =
    match s with
    | Lin -> acc
    | Snoc (r, _) -> go r (acc + 1)
  in
  go s 0

let hd = function
  | Lin -> failwith "Snoc.hd"
  | Snoc (_, x) -> x

let nth s n =
  let rec go s n =
    match s with
    | Lin -> failwith "Snoc.nth"
    | Snoc (xs, x) -> if n = 0 then x else go xs (n - 1)
  in
  go s n

let rec append s v =
  match s with
  | Lin -> Snoc (Lin, v)
  | Snoc _ -> Snoc (s, v)

and ( @> ) s v = append s v

let rec prepend l r =
  match l with
  | Snoc (ls, l) -> prepend ls r @> l
  | Lin -> r

and ( <@ ) l r = prepend l r

let flatten s =
  let rec go s =
    match s with
    | Lin -> Lin
    | Snoc (xs, x) -> x <@ go xs
  in
  go s

let reverse s =
  let rec go s acc =
    match s with
    | Lin -> acc
    | Snoc (xs, x) -> go xs (acc @> x)
  in
  go s empty

let of_list l =
  let rec go l acc =
    match l with
    | [] -> acc
    | x :: xs -> go xs (acc @> x)
  in
  go l Lin

let to_list s =
  let rec go s acc =
    match s with
    | Lin -> acc
    | Snoc (xs, x) -> go xs (x :: acc)
  in
  go s []

let rec map f = function
  | Lin -> Lin
  | Snoc (r, v) -> map f r @> f v

let rec map2 f l r =
  match (l, r) with
  | Lin, Lin -> Lin
  | Snoc (ls, l), Snoc (rs, r) -> map2 f ls rs @> f l r
  | _ -> failwith "Snoc.map2"

let rec fold_left f acc s =
  match s with
  | Lin -> acc
  | Snoc (r, v) -> f (fold_left f acc r) v

let rec fold_right f s acc =
  match s with
  | Lin -> acc
  | Snoc (r, v) -> fold_right f r (f v acc)

let rec find_opt f = function
  | Lin -> None
  | Snoc (xs, x) -> if f x then Some x else find_opt f xs

let find_mapi f s =
  let rec go f s n =
    match s with
    | Lin -> None
    | Snoc (xs, x) -> (
      match f n x with
      | None -> go f xs (n + 1)
      | v -> v)
  in
  go f s 0

let combine_errors s =
  let rec go acc = function
    | Lin -> Some (reverse acc)
    | Snoc (xs, x) -> (
      match x with
      | None -> None
      | Some x -> go (acc @> x) xs)
  in
  go empty s
