(** Bitvector *)

type t

val create : unit -> t

val ensure_size : t -> int -> unit
(** [ensure_size bv i] ensures that [i] is a valid index in [bv] *)

val get : t -> int -> bool
val set : t -> int -> bool -> unit
val clear_all : t -> unit
