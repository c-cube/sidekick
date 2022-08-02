(** Proof traces.

    A proof trace is a log of all the deductive reasoning steps made by
    the SMT solver and other reasoning components. It essentially stores
    a DAG of all these steps, where each step points (via {!step_id})
    to its premises.
*)

open Sidekick_core_logic

type lit = Lit.t

type step_id = Proof_step.id
(** Identifier for a tracing step (like a unique ID for a clause previously
    added/proved) *)

module Step_vec : Vec_sig.BASE with type elt = step_id
(** A vector indexed by steps. *)

(** {2 Traces} *)

type t
(** The proof trace itself.

    A proof trace is a log of all deductive steps taken by the solver,
    so we can later reconstruct a certificate for proof-checking.

    Each step in the proof trace should be a {b valid
    lemma} (of its theory) or a {b valid consequence} of previous steps.
*)

val enabled : t -> bool
(** Is proof tracing enabled? *)

val add_step : t -> Proof_term.delayed -> step_id
(** Create a new step in the trace. *)

val add_unsat : t -> step_id -> unit
(** Signal "unsat" result at the given proof *)

val delete : t -> step_id -> unit
(** Forget a step that won't be used in the rest of the trace.
    Only useful for performance/memory considerations. *)

(** {2 Dummy backend} *)

val dummy_step_id : step_id

val dummy : t
(** Dummy proof trace, logs nothing. *)

(* TODO: something that just logs on stderr? or uses "Log"? *)

(** {2 Dynamic interface} *)

module type DYN = sig
  val enabled : unit -> bool
  val add_step : Proof_term.delayed -> step_id
  val add_unsat : step_id -> unit
  val delete : step_id -> unit
end

val make : (module DYN) -> t
