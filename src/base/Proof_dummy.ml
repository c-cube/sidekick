
open Base_types

type lit = Lit.t
type term = Term.t

type t = unit
type proof_step = unit
type proof_rule = t -> proof_step

module Step_vec = Vec_unit

let create () : t = ()
let with_proof _ _ = ()

let enabled (_pr:t) = false
let del_clause _ _ (_pr:t) = ()
let emit_redundant_clause _ ~hyps:_ _ = ()
let emit_input_clause _ _ = ()
let define_term _ _ _ = ()
let emit_unsat _ _ = ()
let proof_p1 _ _ (_pr:t) = ()
let emit_unsat_core _ (_pr:t) = ()
let lemma_preprocess _ _ ~using:_ (_pr:t) = ()
let lemma_true _ _ = ()
let lemma_cc _ _ = ()
let lemma_rw_clause _ ~res:_ ~using:_ (_pr:t) = ()
let with_defs _ _ (_pr:t) = ()

let lemma_lra _ _ = ()

let lemma_bool_tauto _ _ = ()
let lemma_bool_c _ _ _ = ()
let lemma_bool_equiv _ _ _ = ()
let lemma_ite_true ~ite:_ _ = ()
let lemma_ite_false ~ite:_ _ = ()

let lemma_isa_cstor ~cstor_t:_ _ (_pr:t) = ()
let lemma_select_cstor ~cstor_t:_ _ (_pr:t) = ()
let lemma_isa_split _ _ (_pr:t) = ()
let lemma_isa_sel _ (_pr:t) = ()
let lemma_isa_disj _ _ (_pr:t) = ()
let lemma_cstor_inj _ _ _ (_pr:t) = ()
let lemma_cstor_distinct _ _ (_pr:t) = ()
let lemma_acyclicity _ (_pr:t) = ()
