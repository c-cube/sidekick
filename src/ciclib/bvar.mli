(** Bound variable *)

open Types_

type t = bvar = { bv_idx: int } [@@unboxed]

include EQ_HASH_PRINT with type t := t

val make : int -> t
val idx : t -> int
