module Make (Lit : sig
  type t
end) :
  Solver_intf.PROOF
    with type lit = Lit.t
     and type t = unit
     and type proof_step = unit = struct
  type lit = Lit.t
  type t = unit
  type proof_step = unit
  type proof_rule = t -> proof_step

  module Step_vec = Vec_unit

  let enabled (_pr : t) = false
  let del_clause _ _ (_pr : t) = ()
  let emit_redundant_clause _ ~hyps:_ _ = ()
  let emit_input_clause _ _ = ()
  let emit_unsat _ _ = ()
  let emit_unsat_core _ (_pr : t) = ()
end
