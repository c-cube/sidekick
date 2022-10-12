let name_sat_input = "sat.input"
let name_redundant_clause = "sat.rc"
let name_unsat_core = "sat.uc"

type lit = Lit.t

let sat_input_clause lits : Pterm.t = Pterm.apply_rule name_sat_input ~lits

let sat_redundant_clause lits ~hyps : Pterm.t =
  Pterm.apply_rule name_redundant_clause ~lits ~premises:(Iter.to_rev_list hyps)

let sat_unsat_core lits : Pterm.t = Pterm.apply_rule ~lits name_unsat_core
