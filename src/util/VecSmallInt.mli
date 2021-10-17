
(** Vectors of int32 integers

    These vectors are more optimized than {!Vec}. *)

include Vec_sig.S with type elt := int

val push_i32 : t -> int32 -> unit

val get_i32 : t -> int -> int32

val set_i32 : t -> int -> int32 -> unit

