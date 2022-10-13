module Proof = Sidekick_proof

let lemma_lra lits : Proof.Pterm.t = Proof.Pterm.apply_rule "lra.lemma" ~lits
