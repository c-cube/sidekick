(** Dummy proof module that does nothing. *)

open Base_types

module Arg :
  Sidekick_sigs_proof_trace.ARG with type rule = unit and type step_id = unit

include Sidekick_sigs_proof_trace.S with module A = Arg

type rule = A.rule
type step_id = A.step_id

module Rule_sat :
  Sidekick_sigs_proof_sat.S with type rule = rule and type lit = Lit.t

module Rule_core :
  Sidekick_core.PROOF_CORE
    with type rule = rule
     and type lit = Lit.t
     and type term = Term.t

val create : unit -> t
val lemma_lra : Lit.t Iter.t -> rule

module Rule_data :
  Sidekick_th_data.PROOF_RULES
    with type rule = rule
     and type lit = Lit.t
     and type term = Term.t

module Rule_bool :
  Sidekick_th_bool_static.PROOF_RULES
    with type rule = rule
     and type lit = Lit.t
     and type term = Term.t
     and type term := Term.t
