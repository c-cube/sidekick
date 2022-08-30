type lit = Lit.t

let sat_input_clause lits : Proof_term.t =
  Proof_term.apply_rule "sat.input" ~lits

let sat_redundant_clause lits ~hyps : Proof_term.t =
  Proof_term.apply_rule "sat.rup" ~lits ~premises:(Iter.to_rev_list hyps)

let sat_unsat_core lits : Proof_term.t =
  Proof_term.apply_rule ~lits "sat.unsat-core"
