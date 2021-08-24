
(** Vectors of floats

    These vectors are more optimized than {!Vec}. *)

include Vec_sig.S with type elt := float

val ensure_size : t -> int -> unit
