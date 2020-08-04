# Sidekick [![Build (travis)](https://travis-ci.org/c-cube/sidekick.svg?branch=master)](https://travis-ci.org/c-cube/sidekick) ![Build (gh)](https://github.com/c-cube/sidekick/workflows/Build%20sidekick-bin/badge.svg)

Sidekick is an OCaml library with a functor to create SMT solvers following
the CDCL(T) approach (so called "lazy SMT").

It derives from [Alt-Ergo Zero](http://cubicle.lri.fr/alt-ergo-zero)
and its fork [mSAT](https://github.com/gbury/msat).


## Documentation

See https://c-cube.github.io/sidekick/

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
