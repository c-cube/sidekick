
(** Vectors of floats

    These vectors are more optimized than {!Vec}. *)

type t

val create : unit -> t

val ensure_size : t -> int -> unit

val size : t -> int

val clear : t -> unit

val is_empty : t -> bool

val push : t -> float -> unit

val pop : t -> float

val get : t -> int -> float

val set : t -> int -> float -> unit

val shrink : t -> int -> unit

val iter : f:(float -> unit) -> t -> unit
val iteri : f:(int -> float -> unit) -> t -> unit

val to_iter : t -> float Iter.t

val pp : t CCFormat.printer
