open Sidekick_core

type term = Term.t
type lit = Lit.t

let lemma_bool_tauto lits : Proof_term.t =
  Proof_term.apply_rule "bool.tauto" ~lits

let lemma_bool_c name terms : Proof_term.t =
  Proof_term.apply_rule ("bool.c." ^ name) ~terms

let lemma_bool_equiv t u : Proof_term.t =
  Proof_term.apply_rule "bool.equiv" ~terms:[ t; u ]

let lemma_ite_true ~ite : Proof_term.t =
  Proof_term.apply_rule "bool.ite.true" ~terms:[ ite ]

let lemma_ite_false ~ite : Proof_term.t =
  Proof_term.apply_rule "bool.ite.false" ~terms:[ ite ]
