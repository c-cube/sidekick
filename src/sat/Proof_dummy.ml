(** Dummy proof module using rule=[unit].

    These proof traces will not record anything. *)

module Make (Lit : sig
  type t
end) : sig
  module Proof_trace :
    Sidekick_sigs_proof_trace.S
      with type A.rule = unit
       and type A.step_id = unit
       and type t = unit

  module Proof_rules :
    Solver_intf.PROOF_RULES
      with type lit = Lit.t
       and type rule = unit
       and type step_id = unit
end = struct
  module Proof_trace = Sidekick_proof_trace_dummy.Unit

  module Proof_rules = struct
    type lit = Lit.t
    type rule = unit
    type step_id = unit

    let sat_input_clause _ = ()
    let sat_redundant_clause _ ~hyps:_ = ()
    let sat_unsat_core _ = ()
  end
end
