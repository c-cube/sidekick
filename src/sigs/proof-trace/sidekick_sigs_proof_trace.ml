(** Proof traces.
*)

open Sidekick_util

module type S = sig
  type rule

  type step_id
  (** Identifier for a tracing step (like a unique ID for a clause previously
      added/proved) *)

  module Step_vec : Vec_sig.BASE with type t = step_id
  (** A vector indexed by steps. *)

  (** The proof trace itself.

      A proof trace is a log of all deductive steps taken by the solver,
      so we can later reconstruct a certificate for proof-checking.

      Each step in the proof trace should be a {b valid
      lemma} (of its theory) or a {b valid consequence} of previous steps.
  *)
  module type PROOF_TRACE = sig
    val enabled : unit -> bool
    (** Is proof tracing enabled? *)

    val add_step : rule -> step_id
    (** Create a new step in the trace. *)

    val add_unsat : step_id -> unit
    (** Signal "unsat" result at the given proof *)

    val delete : step_id -> unit
    (** Forget a step that won't be used in the rest of the trace.
        Only useful for performance/memory considerations. *)
  end

  type t = (module PROOF_TRACE)
end

module Utils_ (Trace : S) = struct
  let[@inline] enabled ((module Tr) : Trace.t) : bool = Tr.enabled ()

  let[@inline] add_step ((module Tr) : Trace.t) rule : Trace.step_id =
    Tr.add_step rule

  let[@inline] add_unsat ((module Tr) : Trace.t) s : unit = Tr.add_unsat s
  let[@inline] delete ((module Tr) : Trace.t) s : unit = Tr.delete s
end
