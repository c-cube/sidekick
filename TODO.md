# Goals

## TODO

- theory of boolean constructs (on the fly Tseitin using local clauses)
- make CC work on QF_UF
  * internalize terms on the fly (backtrackable)
  * basic notion of activity (of subterms) for `ite`?
- have `Sat_solver.push_local` work properly

- write Shostak theory of datatypes (without acyclicity) with local case splits
- design evaluation system (guards + `eval_bool:(term -> bool) option` in custom TC)
- compilation of rec functions to defined constants
- add `CC.add_rw_step t u` work, where `t-->u`
  (remove `t` from sig table, should have almost 0 overhead after that)
- theory of defined constants relying on congruence closure + evaluation
  of guards of each case

- Shostak theory of eq-ℚ
- datatype acyclicity check

- abstract domain propagation in CC
- domain propagation (intervals) for ℚ arith
- full ℚ theory: shostak + domains + if-sat simplex

## Main goals

- Add a backend to send proofs to dedukti
    * First, pure resolution proofs
    * Then, require theories to output lemma proofs for dedukti (in some format yet to be decided)
- Allow to plug one's code into boolean propagation
    * react upon propagation (possibly by propagating more, or side-effect)
    * more advanced/specific propagation (2-clauses)?
    * implement 'constraints' (see https://www.lri.fr/~conchon/TER/2013/3/minisat.pdf )

## Long term goals

- max-sat/max-smt
- coq proofs ?


## Done

- remove tseitin lib
- typing and translation Ast -> Term (from mc2?)
- main executable for SMT solver
- base types (Term, Lit, …)
- theory combination
- basic design of theories
