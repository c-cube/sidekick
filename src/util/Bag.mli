(* This file is free software. See file "license" for more details. *)

(** {1 Ordered Bag of Elements}

    A data structure where we can have duplicate elements, optimized for
    fast concatenation and size. *)

type +'a t = private E | L of 'a | N of 'a t * 'a t

val empty : 'a t
val is_empty : _ t -> bool
val return : 'a -> 'a t
val cons : 'a -> 'a t -> 'a t
val snoc : 'a t -> 'a -> 'a t
val append : 'a t -> 'a t -> 'a t
val of_iter : 'a Iter.t -> 'a t
val to_iter : 'a t -> 'a Iter.t
val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val iter : ('a -> unit) -> 'a t -> unit

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(** Are the two bags equal, element wise? *)
