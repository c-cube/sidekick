(** Proof traces.
*)

open Sidekick_util

module type ARG = sig
  type rule

  type step_id
  (** Identifier for a tracing step (like a unique ID for a clause previously
      added/proved) *)

  module Step_vec : Vec_sig.BASE with type elt = step_id
  (** A vector indexed by steps. *)
end

module type S = sig
  module A : ARG

  type t
  (** The proof trace itself.

      A proof trace is a log of all deductive steps taken by the solver,
      so we can later reconstruct a certificate for proof-checking.

      Each step in the proof trace should be a {b valid
      lemma} (of its theory) or a {b valid consequence} of previous steps.
  *)

  val enabled : t -> bool
  (** Is proof tracing enabled? *)

  val add_step : t -> A.rule -> A.step_id
  (** Create a new step in the trace. *)

  val add_unsat : t -> A.step_id -> unit
  (** Signal "unsat" result at the given proof *)

  val delete : t -> A.step_id -> unit
  (** Forget a step that won't be used in the rest of the trace.
      Only useful for performance/memory considerations. *)
end
