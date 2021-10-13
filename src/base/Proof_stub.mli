
(** Dummy proof module that does nothing. *)

open Base_types


include Sidekick_core.PROOF
  with type t = private unit
   and type proof_step = private unit
   and type lit = Lit.t
   and type term = Term.t

type proof_rule = t -> proof_step

val create : unit -> t

val lemma_lra : Lit.t Iter.t -> proof_rule

include Sidekick_th_data.PROOF
  with type proof := t
   and type proof_step := proof_step
   and type lit := Lit.t
   and type term := Term.t

include Sidekick_th_bool_static.PROOF
  with type proof := t
   and type proof_step := proof_step
   and type lit := Lit.t
   and type term := Term.t
