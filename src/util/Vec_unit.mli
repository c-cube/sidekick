(** Fake vector of unit.

  This just retains the size, as 0 bits of actual storage are required. *)

include Vec_sig.S with type elt = unit
