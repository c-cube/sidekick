
(* This file is free software. See file "license" for more details. *)

(** {1 Ordered Bag of Elements}

    A data structure where we can have duplicate elements, optimized for
    fast concatenation and size. *)

type +'a t

val empty : 'a t

val is_empty : _ t -> bool

val return : 'a -> 'a t

val size : _ t -> int
(** Constant time *)

val cons : 'a -> 'a t -> 'a t

val append : 'a t -> 'a t -> 'a t

val to_seq : 'a t -> 'a Sequence.t

val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

val iter : ('a -> unit) -> 'a t -> unit

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(** Are the two bags equal, element wise? *)
