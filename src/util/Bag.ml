(* This file is free software. See file "license" for more details. *)

(** {1 Ordered Bag of Elements}

    A data structure where we can have duplicate elements, optimized for
    fast concatenation and size. *)

type 'a t = E | L of 'a | N of 'a t * 'a t (* size *)

let empty = E

let[@inline] is_empty = function
  | E -> true
  | L _ | N _ -> false

let[@inline] return x = L x

let[@inline] append a b =
  match a, b with
  | E, _ -> b
  | _, E -> a
  | _ -> N (a, b)

let cons x t =
  match t with
  | E -> L x
  | L _ -> N (L x, t)
  | N (_, _) -> N (L x, t)

let snoc t x =
  match t with
  | E -> L x
  | L _ -> N (t, L x)
  | N (_, _) -> N (t, L x)

let of_iter i =
  let r = ref empty in

  i (fun x -> r := snoc !r x);
  !r

let rec fold f acc = function
  | E -> acc
  | L x -> f acc x
  | N (a, b) -> fold f (fold f acc a) b

let[@unroll 2] rec to_iter t yield =
  match t with
  | E -> ()
  | L x -> yield x
  | N (a, b) ->
    to_iter a yield;
    to_iter b yield

let[@inline] iter f t = to_iter t f

let equal f a b =
  let rec push x l =
    match x with
    | E -> l
    | L _ -> x :: l
    | N (a, b) -> push a (b :: l)
  in
  (* same-fringe traversal, using two stacks *)
  let rec aux la lb =
    match la, lb with
    | [], [] -> true
    | E :: _, _ | _, E :: _ -> assert false
    | N (x, y) :: la, _ -> aux (push x (y :: la)) lb
    | _, N (x, y) :: lb -> aux la (push x (y :: lb))
    | L x :: la, L y :: lb -> f x y && aux la lb
    | [], L _ :: _ | L _ :: _, [] -> false
  in
  aux (push a []) (push b [])
