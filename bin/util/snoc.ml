type 'a t =
  | Lin
  | Snoc of 'a t * 'a

let empty = Lin

let length s =
  let rec go s acc =
    match s with
    | Lin -> acc
    | Snoc (r, _) -> go r (acc + 1)
  in
  go s 0

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

let rec fold_left f acc s =
  match s with
  | Lin -> acc
  | Snoc (r, v) -> f (fold_left f acc r) v

let fold_lefti f acc s =
  let rec go f acc n = function
    | Lin -> acc
    | Snoc (r, v) -> f n (go f acc (n + 1) r) v
  in
  go f acc 0 s

let rec fold_right f s acc =
  match s with
  | Lin -> acc
  | Snoc (r, v) -> fold_right f r (f v acc)

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
