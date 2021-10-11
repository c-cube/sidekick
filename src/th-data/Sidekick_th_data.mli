(** Theory for datatypes. *)

include module type of Th_intf

module type S = sig
  module A : ARG
  val theory : A.S.theory
  (** A theory that can be added to {!A.S} to perform datatype reasoning. *)
end

module Make(A : ARG) : S with module A = A
