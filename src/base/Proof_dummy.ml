open Base_types

type lit = Lit.t
type term = Term.t

module Arg = struct
  type nonrec rule = unit
  type nonrec step_id = unit

  module Step_vec = Vec_unit

  let dummy_step_id = ()
end

include Sidekick_proof_trace_dummy.Make (Arg)

type rule = A.rule
type step_id = A.step_id

let create () : t = ()
let with_proof _ _ = ()

module Rule_sat = struct
  type nonrec rule = rule
  type nonrec step_id = step_id
  type nonrec lit = lit

  let sat_redundant_clause _ ~hyps:_ = ()
  let sat_input_clause _ = ()
  let sat_unsat_core _ = ()
end

module Rule_core = struct
  type nonrec rule = rule
  type nonrec step_id = step_id
  type nonrec lit = lit
  type nonrec term = term

  let define_term _ _ = ()
  let proof_p1 _ _ = ()
  let proof_r1 _ _ = ()
  let proof_res ~pivot:_ _ _ = ()
  let lemma_preprocess _ _ ~using:_ = ()
  let lemma_true _ = ()
  let lemma_cc _ = ()
  let lemma_rw_clause _ ~res:_ ~using:_ = ()
  let with_defs _ _ = ()
end

let lemma_lra _ = ()

module Rule_bool = struct
  type nonrec rule = rule
  type nonrec lit = lit

  let lemma_bool_tauto _ = ()
  let lemma_bool_c _ _ = ()
  let lemma_bool_equiv _ _ = ()
  let lemma_ite_true ~ite:_ = ()
  let lemma_ite_false ~ite:_ = ()
end

module Rule_data = struct
  type nonrec rule = rule
  type nonrec lit = lit
  type nonrec term = term

  let lemma_isa_cstor ~cstor_t:_ _ = ()
  let lemma_select_cstor ~cstor_t:_ _ = ()
  let lemma_isa_split _ _ = ()
  let lemma_isa_sel _ = ()
  let lemma_isa_disj _ _ = ()
  let lemma_cstor_inj _ _ _ = ()
  let lemma_cstor_distinct _ _ = ()
  let lemma_acyclicity _ = ()
end
