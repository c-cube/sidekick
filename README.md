# CDCL [![Build Status](https://travis-ci.org/c-cube/cdcl.svg?branch=master)](https://travis-ci.org/c-cube/CDCL)

CDCL is an OCaml library with a functor to create SMT solvers following
the CDCL(T) approach (so called "lazy SMT").

It derives from [Alt-Ergo Zero](http://cubicle.lri.fr/alt-ergo-zero)
and its fork [mSAT](https://github.com/gbury/msat).


## Documentation

See https://c-cube.github.io/cdcl/

## Installation

### Via opam

Once the package is on [opam](http://opam.ocaml.org), just `opam install cdcl`.
For the development version, use:

    opam pin add msat https://github.com/c-cube/cdcl.git

### Manual installation

You will need jbuilder. The command is:

    make install

## Usage

The main module is `CDCL`.

A modular implementation of the SMT algorithm can be found in the `CDCL.Make` functor,
as a functor which takes a `Theory_intf.S` module

## Copyright

This program is distributed under the Apache Software License version
2.0. See the enclosed file `LICENSE`.
