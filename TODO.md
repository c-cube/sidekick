# Goals

## TODO

- per-theory trail, with push/pop as in the SAT solver (generic trail?)
  * in CC, clear pending tasks upon backtrack

- in CC, merge classes eagerly

- rethink backtracking: instead of a pure stack, consider the theory as separated from the SAT solver.
  When a new term is added, unwind theory back to level 0, add term, then up
  to current trail level again.

- in terms, remove `Bool` case and add `Value of value` instead
  **OR**: turn every term into `apply` with a `cst` and a `args: term IArray.t`, make bool such a constant,
    and have `is_value` predicate in custom constants (or `as_value: self -> value option?`)

- when CC merging two classes, if one is a value then pick it as representative
  (i.e. values are always representatives)

- fix:
  ./main.exe tests/unsat/eq_diamond10.smt2

- make CC work on QF_UF
  * public `add` function should push_pending then call main CC loop
    (internal one is called within the loop so no need)
  * internalize terms on the fly (backtrackable) OR: at the beginning, backtrack to 0 to add a new term and then add trail again
  * basic notion of activity (of subterms) for `ite` (and recfuns, later)?

- add `CC.add_rw_step t u` work, where `t-->u`
  (remove `t` from sig table, should have almost 0 overhead after that)
  * use it for `if a b c --> b` when `a=true`
  * use it for local simplifications
  * use it for function evaluation (i.e. rewrite rules)

- write theory of datatypes (without acyclicity) with local case splits + `value` + injectivity
- design evaluation system (guards + `eval:(term -> value) option` in custom TC)
- compilation of rec functions to defined constants
- theory of defined constants relying on congruence closure + evaluation
  of guards of each case

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

- simplify CC by separating cleanly public/internal API, remove excess batching
- notion of `value` (V_true,V_false,V_custom, + maybe undefined some day)
- checking models (for each clause, at least one true lit also evals to true in model)
  * have a `function` section in the model with `(id*value list) -> value`,
    extracted from congruence closure
- simplify terms a lot, remove solving/semantic terms
- remove `detach_clause`. never detach a clause until it's really dead;
  instead, do (and re-do) `internalize_clause` for its atoms.
- remove push/pop
- merge Solver_types.ml with Internal.ml
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
