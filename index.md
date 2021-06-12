# Sidekick

Sidekick is an OCaml framework to implement and use
[SMT solvers](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
based on [CDCL](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning).

It is heavily functorized (parametrized) so it can use user-provided data structures,
term representation, etc. and each part is _potentially_ swappable, even the SAT solver.

Sidekick is composed of a few libraries:

- `sidekick` contains the core type definitions, a congruence closure,
  some theories (boolean formuals, algebraic datatypes),
  and a solver implementation based on [mSAT](https://github.com/Gbury/mSAT).

  `Sidekick_core` is the most important module to read there.
- `sidekick-arith` depends on [Zarith](https://github.com/ocaml/Zarith)
  for arbitrary-precision computations, and provides a LRA theory based
  on an implementation of the Simplex algorithm.
- `sidekick-bin` is an executable that uses the previous building blocks
  to implement a concrete SMT solver. It is useful for testing, but
  can also be used as a normal SMT solver on the command line.

  It contains examples of how to instantiate the functors of `sidekick`
  and `sidekick-arith`.

## API Documentation

- [development docs](dev/index.html) (docs following the master branch)
