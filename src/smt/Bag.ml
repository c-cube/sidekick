
(* This file is free software. See file "license" for more details. *)

(** {1 Ordered Bag of Elements}

    A data structure where we can have duplicate elements, optimized for
    fast concatenation and size. *)

type 'a t =
  | E
  | L of 'a
  | N of 'a t * 'a t * int (* size *)

let empty = E

let is_empty = function
  | E -> true
  | L _ | N _ -> false

let size = function
  | E -> 0
  | L _ -> 1
  | N (_,_,sz) -> sz

let return x = L x

let append a b = match a, b with
  | E, _ -> b
  | _, E -> a
  | _ -> N (a, b, size a + size b)

let cons x t = match t with
  | E -> L x
  | L _ -> N (L x, t, 2)
  | N (_,_,sz) -> N (L x, t, sz+1)

let rec fold f acc = function
  | E -> acc
  | L x -> f acc x
  | N (a,b,_) -> fold f (fold f acc a) b

let rec to_seq t yield = match t with
  | E -> ()
  | L x -> yield x
  | N (a,b,_) -> to_seq a yield; to_seq b yield

let iter f t = to_seq t f

let equal f a b =
  let rec push x l = match x with
    | E -> l
    | L _ -> x :: l
    | N (a,b,_) -> push a (b::l)
  in
  (* same-fringe traversal, using two stacks *)
  let rec aux la lb = match la, lb with
    | [], [] -> true
    | E::_, _ | _, E::_ -> assert false
    | N (x,y,_)::la, _ -> aux (push x (y::la)) lb
    | _, N(x,y,_)::lb -> aux la (push x (y::lb))
    | L x :: la, L y :: lb -> f x y && aux la lb
    | [], L _::_
    | L _::_, [] -> false
  in
  size a = size b &&
  aux (push a []) (push b [])

