(* FIXME
   open Proof_trace

   type lit = Lit.t
*)

type lit = Lit.t

let lemma_cc lits : Proof_term.t = Proof_term.make ~lits "core.lemma-cc"

let define_term t1 t2 =
  Proof_term.make ~terms:(Iter.of_list [ t1; t2 ]) "core.define-term"

let proof_r1 p1 p2 =
  Proof_term.make ~premises:(Iter.of_list [ p1; p2 ]) "core.r1"

let proof_p1 p1 p2 =
  Proof_term.make ~premises:(Iter.of_list [ p1; p2 ]) "core.p1"

let proof_res ~pivot p1 p2 =
  Proof_term.make ~terms:(Iter.return pivot)
    ~premises:(Iter.of_list [ p1; p2 ])
    "core.res"

let with_defs pr defs =
  Proof_term.make ~premises:(Iter.append (Iter.return pr) defs) "core.with-defs"

let lemma_true t = Proof_term.make ~terms:(Iter.return t) "core.true"

let lemma_preprocess t1 t2 ~using =
  Proof_term.make
    ~terms:(Iter.of_list [ t1; t2 ])
    ~premises:using "core.preprocess"

let lemma_rw_clause pr ~res ~using =
  Proof_term.make
    ~premises:(Iter.append (Iter.return pr) using)
    ~lits:res "core.rw-clause"
