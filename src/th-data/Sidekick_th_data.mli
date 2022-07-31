(** Theory for datatypes. *)

include module type of Th_intf

val make : (module ARG) -> SMT.theory
