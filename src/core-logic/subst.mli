(** Substitutions *)

open Types_

type t = subst

include PRINT with type t := t

val empty : t
val is_empty : t -> bool
val of_list : (var * term) list -> t
val of_iter : (var * term) Iter.t -> t
val to_iter : t -> (var * term) Iter.t
val add : var -> term -> t -> t
val apply : Term.store -> recursive:bool -> t -> term -> term
