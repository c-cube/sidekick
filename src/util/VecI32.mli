
(** Vectors of int32 integers

    These vectors are more optimized than {!Vec}. *)

type t

val create : ?cap:int -> unit -> t

val ensure_size : t -> int -> unit

val size : t -> int

val clear : t -> unit

val is_empty : t -> bool

val push : t -> int -> unit

val pop : t -> int

val push_i32 : t -> int32 -> unit

val get : t -> int -> int

val get_i32 : t -> int -> int32

val set : t -> int -> int -> unit

val set_i32 : t -> int -> int32 -> unit

val shrink : t -> int -> unit

val iter : f:(int -> unit) -> t -> unit
val iteri : f:(int -> int -> unit) -> t -> unit

module Slice : sig
  type t

  val size : t -> int
  val get : t -> int -> int
  val set : t -> int -> int -> unit
  val swap : t -> int -> int -> unit
end

val slice : t -> off:int -> len:int -> Slice.t

val to_iter : t -> int Iter.t

val pp : t CCFormat.printer
