module type ARG = Sidekick_sigs_proof_trace.ARG
module type S = Sidekick_sigs_proof_trace.S

(** Dynamic version.

    The proof trace is a first-class module that can be provided at runtime. *)
module Make_dyn (A : ARG) : S with module A = A = struct
  module A = A

  module type DYN = sig
    val enabled : unit -> bool
    val add_step : A.rule -> A.step_id
    val add_unsat : A.step_id -> unit
    val delete : A.step_id -> unit
  end

  type t = (module DYN)

  let[@inline] enabled ((module Tr) : t) : bool = Tr.enabled ()
  let[@inline] add_step ((module Tr) : t) rule : A.step_id = Tr.add_step rule
  let[@inline] add_unsat ((module Tr) : t) s : unit = Tr.add_unsat s
  let[@inline] delete ((module Tr) : t) s : unit = Tr.delete s
end
