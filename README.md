# dagon [![Build Status](https://travis-ci.org/c-cube/cdcl.svg?branch=master)](https://travis-ci.org/c-cube/CDCL)

Dagon is an OCaml library with a functor to create SMT solvers following
the CDCL(T) approach (so called "lazy SMT").

It derives from [Alt-Ergo Zero](http://cubicle.lri.fr/alt-ergo-zero)
and its fork [mSAT](https://github.com/gbury/msat).


## Documentation

See https://c-cube.github.io/dagon/

## Installation

### Via opam

Once the package is on [opam](http://opam.ocaml.org), just `opam install dagon`.
For the development version, use:

    opam pin add dagon https://github.com/c-cube/dagon.git

### Manual installation

You will need jbuilder. The command is:

    make install

## Copyright

This program is distributed under the Apache Software License version
2.0. See the enclosed file `LICENSE`.
