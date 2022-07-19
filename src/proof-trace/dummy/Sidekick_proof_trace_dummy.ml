module type S = Sidekick_sigs_proof_trace.S

module type ARG = sig
  include Sidekick_sigs_proof_trace.ARG

  val dummy_step_id : step_id
end

module Make (A : ARG) : S with type t = unit and module A = A = struct
  module A = A

  type t = unit

  let enabled _ = false
  let add_step _ _ = A.dummy_step_id
  let add_unsat _ _ = ()
  let delete _ _ = ()
end
