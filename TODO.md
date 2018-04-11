# Goals

## TODO

- SAT:
  * merge all clause vectors into one
  * remove all simplifications at level 0
  * addition of clauses: should be much simpler

- explicit lifecycle for SAT atoms  (dead/assigned/in-heap)
- simplify addition of clauses:
  * do not simplify at level 0
  * steps on addition:
    1. internalize all atoms (dead -> in-heap)
    2. unit-propagate/do nothing/add clause
    3. remove clause on backtracking if not at level 0

- merge Solver_types.ml with Internal.ml
- make CC work on QF_UF
  * internalize terms on the fly (backtrackable)
  * basic notion of activity (of subterms) for `ite` (and recfuns, later)?

- redo_down_to_level_0 should actually redo down to `base_level`

- add `CC.add_rw_step t u` work, where `t-->u`
  (remove `t` from sig table, should have almost 0 overhead after that)
  * use it for 

- notion of `value` (V_true,V_false,V_custom, + maybe undefined some day)
- write theory of datatypes (without acyclicity) with local case splits + `value` + injectivity
- design evaluation system (guards + `eval:(term -> value) option` in custom TC)
- compilation of rec functions to defined constants
- theory of defined constants relying on congruence closure + evaluation
  of guards of each case

- datatype acyclicity check

- Shostak theory of eq-ℚ

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

- theory of boolean constructs (on the fly Tseitin using local clauses)
  * test `Sat_solver.add_clause` and `new_atom` behavior upon backtracking
    → when we backtrack an atom, its Tseitin encoding should be removed
  * NOTE: clauses should never be added twice
    (or else: what if a clause is added, removed (but not filtered from watched lits) then re-added? duplicate?)
- backtrackable addition of clauses/atoms in Sat solver
- remove tseitin lib
- typing and translation Ast -> Term (from mc2?)
- main executable for SMT solver
- base types (Term, Lit, …)
- theory combination
- basic design of theories
