open Sidekick_core

let lemma_lra lits : Proof_term.t = Proof_term.apply_rule "lra.lemma" ~lits
