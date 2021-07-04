# Sidekick [![Build](https://github.com/c-cube/sidekick/actions/workflows/main.yml/badge.svg)](https://github.com/c-cube/sidekick/actions/workflows/main.yml)

Sidekick is an OCaml library with a functor to create SMT solvers following
the CDCL(T) approach (so called "lazy SMT"). See [below](#short-summary)
for a more detailed explanation.

It derives from [Alt-Ergo Zero](http://cubicle.lri.fr/alt-ergo-zero)
and its fork [mSAT](https://github.com/gbury/msat).

## Documentation

See [the API documentation](https://c-cube.github.io/sidekick/).

A work-in-progress [guide](doc/guide.md) provides a more step-by-step
introduction to how to use and modify sidekick.

## Short summary

[SMT solvers](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
are automatic tools that try to assess whether a given logic formula is
*satisfiable* (admits a model, an interpretation that makes it true)
or *unsatisfiable* (no interpretation can make it true; it is absurd, and its
negation is a theorem). Prominent solvers include [Z3](https://github.com/Z3Prover/z3),
[cvc5](https://cvc5.github.io/), [Yices 2](https://github.com/SRI-CSL/yices2/),
and others; all of them follow the **CDCL(T)** paradigm.
Most of these solvers are implemented in C or C++.

CDCL(T) is the combination of [CDCL](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning),
the leading technique for SAT solving (as popularized by Chaff, minisat, etc.
in the early oughties), and a **theory** T. In practice, SMT solvers _combine_
multiple theories into one before doing the combination with the SAT solver.
Some examples of theories are uninterpreted functions symbols, integer linear
arithmetic ("LIA"), rational nonlinear arithmetic ("NRA"), bitvectors for fixed-size
arithmetic, algebraic datatypes, and others.

Sidekick is a CDCL(T) solver implemented in pure [OCaml](https://ocaml.org/)
and with a strong focus on modularity and reusability of components.
Almost everything in the code is _functorized_ and generic over the concrete
representation of terms, formulas, etc.
The goal is for users to be able to implement their own theories and combine
them with the pre-existing ones in a bespoke solver, something that is typically
a lot of work in the C/C++ solvers.

Sidekick comes in several components (as in, opam packages):

- `sidekick` is the core library, with core type definitions (see `src/core/`),
  an implementation of CDCL(T) based on [mSat](https://github.com/Gbury/mSAT/),
  a congruence closure, and the theories of boolean formulas, LRA (linear rational
  arithmetic, using a simplex algorithm), and datatypes.
- `sidekick-base` is a library with concrete implementations for terms,
  arithmetic functions, and proofs.
  It comes with an additional dependency on
  [zarith](https://github.com/ocaml/Zarith) to represent numbers (zarith is a
  GMP wrapper for arbitrary precision numbers).
- `sidekick-bin` is an executable that is able to parse problems in
  the SMT-LIB-2.6 format, in the `QF_UFLRA` fragment, and solves them using
  `sidekick` instantiated with `sidekick-base`.
  It is mostly useful as a test tool for the libraries and as a starting point
  for writing custom solvers.

## Installation

### Via opam

Once the package is on [opam](http://opam.ocaml.org), just `opam install sidekick`.
For the development version, use:

    opam pin https://github.com/c-cube/sidekick.git

### Manual installation

You will need dune . The command is:

    make install

## Copyright

This program is distributed under the Apache Software License version
2.0. See the enclosed file `LICENSE`.
