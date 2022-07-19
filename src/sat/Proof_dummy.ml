(** Dummy proof module for rule=empty *)

module Make (Lit : sig
  type t
end) :
  Solver_intf.PROOF_RULES
    with type lit = Lit.t
     and type rule = unit
     and type step_id = unit = struct
  type lit = Lit.t
  type rule = unit
  type step_id = unit

  let sat_input_clause _ = ()
  let sat_redundant_clause _ ~hyps:_ = ()
  let sat_unsat_core _ = ()
end
