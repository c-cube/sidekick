module Proof = Sidekick_proof

let lemma_isa_cstor ~cstor_t t : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~terms:[ cstor_t; t ] "data.isa-cstor"

let lemma_select_cstor ~cstor_t t : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~terms:[ cstor_t; t ] "data.select-cstor"

let lemma_isa_split t lits : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~terms:[ t ] ~lits "data.isa-split"

let lemma_isa_sel t : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~terms:[ t ] "data.isa-sel"

let lemma_isa_disj l1 l2 : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~lits:[ l1; l2 ] "data.isa-disj"

let lemma_cstor_inj t1 t2 i : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~terms:[ t1; t2 ] ~indices:[ i ] "data.cstor-inj"

let lemma_cstor_distinct t1 t2 : Proof.Pterm.t =
  Proof.Pterm.apply_rule ~terms:[ t1; t2 ] "data.cstor-distinct"

let lemma_acyclicity ts : Proof.Pterm.t =
  Proof.Pterm.apply_rule
    ~terms:(CCList.flat_map (fun (t1, t2) -> [ t1; t2 ]) ts)
    "data.acyclicity"
