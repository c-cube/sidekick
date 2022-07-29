(** Basic bitfield *)

type t = private int
type field
type bitfield_gen

val empty : t
val equal : t -> t -> bool
val mk_field : bitfield_gen -> field
val mk_gen : unit -> bitfield_gen
val get : field -> t -> bool
val set : field -> bool -> t -> t
val merge : t -> t -> t
