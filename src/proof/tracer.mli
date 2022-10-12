(** Proof traces.

    A proof trace is a log of all the deductive reasoning steps made by
    the SMT solver and other reasoning components. It essentially stores
    a DAG of all these steps, where each step points (via {!step_id})
    to its premises.
*)

type step_id = Step.id
(** Identifier for a tracing step (like a unique ID for a clause previously
    added/proved) *)

(** A proof tracer.

    A proof tracer builds a log of all deductive steps taken by the solver,
    so we can later reconstruct a certificate for proof-checking.

    Each step in the proof trace should be a {b valid
    lemma} (of its theory) or a {b valid consequence} of previous steps.
*)
class type t =
  object
    method proof_enabled : bool
    (** If proof tracing enabled? *)

    method emit_proof_step : Pterm.delayed -> step_id
    (** Create a new step in the trace. *)

    method emit_proof_delete : step_id -> unit
    (** Forget a step that won't be used in the rest of the trace.
        Only useful for performance/memory considerations. *)
  end

val enabled : #t -> bool
(** Is proof tracing enabled? *)

val add_step : #t -> Pterm.delayed -> step_id
(** Create a new step in the trace. *)

val delete : #t -> step_id -> unit
(** Forget a step that won't be used in the rest of the trace.
    Only useful for performance/memory considerations. *)

class dummy : t
(** Dummy proof trace, logs nothing. *)

val dummy : t

class concrete : sink:Sidekick_trace.Sink.t -> t
(** Concrete implementation of [t] *)
