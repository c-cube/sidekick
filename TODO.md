
## TODO

### 2022-07-20

- cc:
  * fail on reentrant call (like concurrentModifExn in java)
  * in events, provide an `EventAction.t` object rather than the CC;
    it provides find,is_eq,explain_eq,etc. as well as modifications
    that are pushed into the queue instead of done on the fly.

    main thrust: plugins all observe the same immutable CC, their changes are
    performed in batch afterwards
  * egg: provide an extended CC plugin API instead (with enough hooks that
    it can implement the recompute-if-children-changed thing + early exit
    if data didn't change)
  * egg: CC provides a associated data API; hide bitfields, just provide
    a `make_sparse_data`
    + `get: node -> data option`
    + `set: node -> data -> unit` (delayed, use an action queue)
    + automatic backtracking
    ⇒ this should be enough to implement current plugins or even egg itself
  * go beyond egg so that the merge `is-some(t) = true` can modify the class
    of `t`
  * use this to implement booleans! remove true/false custom code
- cc proofs:
  * do not ask for `proof_trace` or rules
    + instead ask for a type of custom explanations (with pp)
    + custom expls are used for both theory in-CC propagations, and
      for model construction (semantic merges)
  * provide own type of proofs, shaped as an indexed list of steps
  * each step proves `t=u` from previous steps using a rule
  * rules are Horn hyper-resolution, congruence, by-assertion(lit),
    trans(list of steps), or custom(custom_expl)
  * theory propagations are annotated with a custom expl and a (T-valid) horn clause
    whose head is the propagated equation

### old

- self-contained proofs (add axioms and type declarations)

- add Egg
  * use for existing theories (at least datatypes)
  * integrate proofs using cc-lemma (no resolution, no intermediate clause)

- new proofs:
  * simplify : use subproof (maybe not even there?)
  * preprocess: no subproof
  * rule for proving `t=u` by CC modulo all previous unit equalities (needed
    for simp/preprocess)
  * [x] to prove `if a b b = b`, do `a => if a b b = b`,
    `¬a => if a b b = b`, and use resolution on these to remove conditions.

- stronger preprocessing:
  * first, split conjunction eagerly
  * add every toplevel `x=t` where x atomic to a congruence closure;
    then replace toplevel `assert p` with `assert [p]` where `[p]` is
    the nested representative of `p` (replace each subterm by its representative).
    proof is just `x1=t1 … xn=tn |- p=[p]`
  * using Egg, should be possible to integrate theory preprocessing this way

  * then:
    - one-point rule for LRA and UF (`x = t /\ F[x]` becomes `x=t /\ F[t]` and
      we forget `x` in practice)
    - eliminate LRA equations true at level 0  (why is alt-ergo faster on uart7?)
    - preprocess LRA for:
      `./sidekick tests/unsat/pb_real_50_150_30_47.smt2`
      `./sidekick tests/unsat/clocksynchro_9clocks.main_invar.base.smt2`

- sidekick-check:
  * implement deletion
  * seems like drat-trim is much faster in backward checking mode, see why
  * implement checking of CC/preprocess
  * checking of LRA
  * checking of DT

- proof production:
  * [x] produce Quip
  * [x] have it proofchecked
  * [x] do not produce stuff like `(cc-imply (refl tseitin0) (= tseitin0 <the term>))`
  * [x] do not produce stuff like `(hres (init (assert t)) (p1 (refl t)))`
        (just `assert t` is enough)
  * [ ] theory lemmas

- [x] functor for mapping equiv classes to values of some monoid, code to be
  used in 99% of the theories
  * [ ] also allow to register to "joins" between distinct classes
    (useful for injectivity or array reduction or selector reduction)
    → in a way this must become a (backtracking) query API for making theories
      easy to write
  * [x] use it in th-data for cstors
  * [x] use it in th-data for select
  * [x] use it in th-data for is-a
  * [ ] use it in th-array
  * [ ] use it in th-define-subsort
  ⇒ **NOTE** this is actually subsumed by Egg


- provide a notion of smtlib theory, with `smtlib.ast --> Term.t option`
  and typing rule (extensible parsing+typing)
  * use if for th-bool
  * use if for th-distinct

- cleanup of CC/optims
  * store lits directly in (boolean) classes

- add terms of input goals pre-emptively to the CC/theories

- add `CC.add_rw_step t u` work, where `t-->u`
  (keep `t` in sig table, but flag is so it's inert and will not
   be pushed into `cc.pending` ever, should have almost 0 overhead after that)
  * use it for local simplifications
  * use it for function evaluation (i.e. rewrite rules)

- design evaluation system (guards + `eval:(term -> value) option` in custom TC)
- compilation of rec functions to defined constants
- theory of defined constants relying on congruence closure + evaluation
  of guards of each case

- abstract domain propagation in CC
- domain propagation (intervals) for ℚ arith

## Main goals

- Allow to plug one's code into boolean propagation
    * react upon propagation (possibly by propagating more, or side-effect)
    * more advanced/specific propagation (2-clauses)?
    * implement 'constraints' (see https://www.lri.fr/~conchon/TER/2013/3/minisat.pdf )

## Long term goals

- max-sat/max-smt
- coq proofs ?

## Done

- refactor:
  * revamp msat proofs
    (store proofs in allocator, also encoded as 0-terminated series of ints
     indicating clause numbers?
     this way we can GC them just like we GC clauses)
      ⇒ keep arrays, simpler
    + means the type of proofs is independent of variables
    + actually: try to use RUP (side buffer to store a representation of
      a list of clauses, each "line" is `c_i := l1…ln 0` like dimacs.
      Add delete lines to get DRUP.)
      proof reconstruction to get, _if wanted_, proper resolution.
    + or just store clause premises in a set, use local RUP to reconstruct
      (assert ¬C and propagate)
  * fix proof production for minimized conflicts (or come back after proof are better)
- enable conflict minimization (from branch) in SAT solver
- emit proofs for SMT;
  * [x] add a clause preprocessing rule
    (combines all the `… |- t=u`
    proofs for preprocessing literals, to rewrite C into D)
  * [x] add a RUP rule into Quip, with explicit hyps (fast but more lenient
    than resolution with explicit order+pivots) ⇒ used in SAT solver
  * [x] store proof in temp file, then parse it backward (using adequate framing)
    to obtain relevant part in memory and produce Quip file
- dyn-trans for CC: add hooks in CC explanation of conflict
  so the theory can intercept that
- write theory of datatypes (without acyclicity) with local case splits + injectivity + selectors
- datatype acyclicity check
- make CC work on QF_UF
  * [x] public `add` function should push_pending then call main CC loop
    (internal one is called within the loop so no need)
  * [x] internalize terms on the fly (backtrackable) OR: at the beginning, backtrack to 0 to add a new term and then add trail again
  * ~~[ ] basic notion of activity (of subterms) for `ite` (and recfuns, later)?~~
- use `stmlib-utils`
- parser for cstors  (`declare-cstor`, same as `declare-fun`)
- refactor:
 1. have sidekick.env with only the signature that is instance-dependent + notion of theory (as module sig);
 2. solver takes this env and SAT solver with compatible lits
 3. move concrete terms, etc. into smtlib lib
 4. update theories
- fix: have normal theories `on_new_term` work properly (callback in the CC?)
- proper statistics
- make the core library entirely functorized
  * current term/cst/lit/… would become an implementation library to
    be used in the binary
- theory for `ite`
- theory for constructors
- do a `th-distinct` package
  * in CC, use payload to store set of distinct tags (if non empty)
  * if `¬distinct(t1…tn)` asserted, make big disjunction of cases (split on demand)
- in CC, store literal associated with term, for bool propagation
- in CC, propagation of boolean terms
- in CC, merge classes eagerly
- when CC merging two classes, if one is a value then pick it as representative
  (i.e. values are always representatives)
- large refactoring of CC
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

## Cancelled

- dynamic ackermannization and transitivity (and maybe datatype acyclicity)
  * clause pool for each type of dynamic inference (dynamic ack, etc.), with
    its own GC limit.
  * Probably need removable atoms too, once all clauses containing it are gone,
    for atoms not added by the user explicitely.
