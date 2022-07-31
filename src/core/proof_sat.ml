type lit = Lit.t

let sat_input_clause lits : Proof_term.data =
  Proof_term.make_data "sat.input" ~lits

let sat_redundant_clause lits ~hyps : Proof_term.data =
  Proof_term.make_data "sat.rup" ~lits ~premises:(Iter.to_rev_list hyps)

let sat_unsat_core lits : Proof_term.data =
  Proof_term.make_data ~lits "sat.unsat-core"
