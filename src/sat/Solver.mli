(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** SAT safe interface

    This module defines a safe interface for the core solver.
    It is the basis of the {!module:Solver} and {!module:Mcsolver} modules.
*)

module type S = Solver_intf.S
(** Safe external interface of solvers. *)

module Make(Th : Theory_intf.S)
  : S with type formula = Th.formula
       and type theory = Th.t
       and type lemma = Th.proof
(** Functor to make a safe external interface. *)


