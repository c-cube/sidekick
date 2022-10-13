open Sidekick_core
module Proof = Sidekick_proof

type term = Term.t
type lit = Lit.t

let lemma_bool_tauto lits : Proof.Pterm.t =
  Proof.Pterm.apply_rule "bool.tauto" ~lits

let lemma_bool_c name terms : Proof.Pterm.t =
  Proof.Pterm.apply_rule ("bool.c." ^ name) ~terms

let lemma_bool_equiv t u : Proof.Pterm.t =
  Proof.Pterm.apply_rule "bool.equiv" ~terms:[ t; u ]

let lemma_ite_true ~ite : Proof.Pterm.t =
  Proof.Pterm.apply_rule "bool.ite.true" ~terms:[ ite ]

let lemma_ite_false ~ite : Proof.Pterm.t =
  Proof.Pterm.apply_rule "bool.ite.false" ~terms:[ ite ]
