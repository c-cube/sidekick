(** {2 Literals} *)

open Base_types

type t = lit = {
  lit_term: term;
  lit_sign : bool
}

val neg : t -> t
val abs : t -> t
val sign : t -> bool
val term : t -> term
val as_atom : t -> term * bool
val atom : Term.state -> ?sign:bool -> term -> t
val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool
val print : t Fmt.printer
val pp : t Fmt.printer
val apply_sign : t -> bool -> t
val norm_sign : t -> t * bool
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t

