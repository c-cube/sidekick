(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** Create SAT/SMT Solvers

    This module provides a functor to create an SMT solver. Additionally, it also
    gives a functor that produce an adequate empty theory that can be given to the [Make]
    functor in order to create a pure SAT solver.
*)

module type S = Msat.S
(** The interface of instantiated solvers. *)

module Make (Th : Theory_intf.S)
  : S with type formula = Th.formula
       and type Proof.lemma = Th.proof
       and type theory = Th.t
(** Functor to create a SMT Solver parametrised by the atomic
    formulas and a theory. *)

