
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

module Proof : sig
  type t = Proof
end

include CDCL.Theory_intf.S
  with type formula = Lit.t
   and type proof = Proof.t

val cc : t -> Congruence_closure.t
val tst : t -> Term.state
val theories : t -> Theory.state Sequence.t

val add_theory : t -> Theory.t -> unit
(** How to add new theories *)

val add_theory_l : t -> Theory.t list -> unit
