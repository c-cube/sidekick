(** Bound variable *)

open Types_

type t = bvar = { bv_idx: int; bv_ty: term }

include EQ_HASH_PRINT with type t := t

val make : int -> term -> t
val ty : t -> term
