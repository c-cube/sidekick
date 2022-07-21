(** Dummy proof traces.

    These proof traces will not record information. *)

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

(** Dummy proof trace where everything is [unit]. Use this if you don't care
   for proofs at all. *)
module Unit :
  S with type t = unit and type A.rule = unit and type A.step_id = unit =
Make (struct
  type rule = unit
  type step_id = unit

  module Step_vec = Vec_unit

  let dummy_step_id = ()
end)
