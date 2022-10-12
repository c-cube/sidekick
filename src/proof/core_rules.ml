(* FIXME
   open Proof_trace

   type lit = Lit.t
*)

type lit = Lit.t

let lemma_cc lits : Pterm.t = Pterm.apply_rule ~lits "core.lemma-cc"
let define_term t1 t2 = Pterm.apply_rule ~terms:[ t1; t2 ] "core.define-term"
let proof_r1 p1 p2 = Pterm.apply_rule ~premises:[ p1; p2 ] "core.r1"
let proof_p1 p1 p2 = Pterm.apply_rule ~premises:[ p1; p2 ] "core.p1"

let proof_res ~pivot p1 p2 =
  Pterm.apply_rule ~terms:[ pivot ] ~premises:[ p1; p2 ] "core.res"

let with_defs pr defs = Pterm.apply_rule ~premises:(pr :: defs) "core.with-defs"
let lemma_true t = Pterm.apply_rule ~terms:[ t ] "core.true"

let lemma_preprocess t1 t2 ~using =
  Pterm.apply_rule ~terms:[ t1; t2 ] ~premises:using "core.preprocess"

let lemma_rw_clause pr ~res ~using =
  Pterm.apply_rule ~premises:(pr :: using) ~lits:res "core.rw-clause"
