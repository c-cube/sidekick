type lit = Lit.t

let sat_input_clause lits : Proof_term.t = Proof_term.make "sat.input" ~lits

let sat_redundant_clause lits ~hyps : Proof_term.t =
  Proof_term.make "sat.rup" ~lits ~premises:hyps

let sat_unsat_core lits : Proof_term.t = Proof_term.make ~lits "sat.unsat-core"
