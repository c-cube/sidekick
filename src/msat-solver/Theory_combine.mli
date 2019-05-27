
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

module Proof : sig
  type t = Solver_types.proof (* dummy proofs, for now *)
end

include Msat.Solver_intf.PLUGIN_CDCL_T
  with module Formula = Lit
   and type proof = Proof.t

val create : ?stat:Stat.t -> unit -> t

val cc : t -> CC.t
val tst : t -> Term.state

type theory_state =
  | Th_state : ('a Theory.t1 * 'a) -> theory_state

val theories : t -> theory_state Iter.t

val mk_model : t -> Lit.t Iter.t -> Model.t

val add_theory : t -> Theory.t -> unit
(** How to add new theories *)

val add_theory_l : t -> Theory.t list -> unit
