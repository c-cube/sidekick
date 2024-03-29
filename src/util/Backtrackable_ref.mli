(** {1 Backtrackable ref} *)

type 'a t

val create : ?copy:('a -> 'a) -> 'a -> 'a t
(** Create a backtrackable reference holding the given value initially.
    @param copy if provided, will be used to copy the value when [push_level]
    is called. *)

val set : 'a t -> 'a -> unit
(** Set the reference's current content *)

val get : 'a t -> 'a
(** Get the reference's current content *)

val update : 'a t -> ('a -> 'a) -> unit
(** Update the reference's current content *)

include Sidekick_sigs.BACKTRACKABLE1 with type 'a t := 'a t
