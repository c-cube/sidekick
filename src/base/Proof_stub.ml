
open Base_types

type lit = Lit.t
type term = Term.t

type t = unit
type dproof = t -> unit

let create () : t = ()
let enabled _ = false

let begin_subproof _ = ()
let end_subproof _ = ()
let del_clause _ _ = ()
let emit_redundant_clause _ _ = ()
let emit_input_clause _ _ = ()
let define_term _ _ _ = ()
let lemma_preprocess _ _ _ = ()
let lemma_true _ _ = ()
let lemma_cc _ _ = ()
let lemma_lra _ _ = ()
let lemma_cstor_inj _ _ = ()
let lemma_isa_disj _ _ = ()
let lemma_isa_split _ _ = ()
let lemma_bool_tauto _ _ = ()
let lemma_bool_c _ _ _ = ()
let lemma_bool_equiv _ _ _ = ()
let lemma_ite_true _ ~a:_ ~ite:_  = ()
let lemma_ite_false _ ~a:_ ~ite:_  = ()
