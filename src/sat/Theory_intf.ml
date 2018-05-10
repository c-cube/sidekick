(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Evelyne Contejean                    *)
(*                  Francois Bobot, Mohamed Iguernelala, Alain Mebsout    *)
(*                  CNRS, Universite Paris-Sud 11                         *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)
(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

(** SMT Theory

    This module defines what a theory must implement in order to
    be used in an SMT solver.
*)

(** This type is used during the normalisation of formulas.
    See {!val:Expr_intf.S.norm} for more details. *)
type negated =
  | Negated     (** changed sign *)
  | Same_sign   (** kept sign *)

(** Type returned by the theory. Formulas in the unsat clause must come from the
    current set of assumptions, i.e must have been encountered in a slice. *)
type ('formula, 'proof) res =
  | Sat
  (** The current set of assumptions is satisfiable. *)
  | Unsat of 'formula list * 'proof
  (** The current set of assumptions is *NOT* satisfiable, and here is a
      theory tautology (with its proof), for which every literal is false
      under the current assumptions. *)

(** Actions given to the theory during initialization, to be used
    at any time *)
type ('form, 'proof) actions = Actions of {
  push_persistent : 'form IArray.t -> 'proof -> unit;
  (** Allows to add a persistent clause to the solver. *)

  push_local : 'form IArray.t -> 'proof -> unit;
  (** Allows to add a local clause to the solver. The clause
      will be removed after backtracking. *)

  on_backtrack: (unit -> unit) -> unit;
  (** [on_backtrack f] calls [f] when the main solver backtracks *)

  propagate : 'form -> 'form list -> 'proof -> unit;
  (** [propagate lit causes proof] informs the solver to propagate [lit], with the reason
      that the clause [causes => lit] is a theory tautology. It is faster than pushing
      the associated clause but the clause will not be remembered by the sat solver,
      i.e it will not be used by the solver to do boolean propagation. *)
}

type ('form, 'proof) slice_actions = Slice_acts of {
  slice_iter : ('form -> unit) -> unit;
  (** iterate on the slice of the trail *)
}
(** The type for a slice. Slices are some kind of view of the current
    propagation queue. They allow to look at the propagated literals,
    and to add new clauses to the solver. *)

(** {2 Signature for theories to be given to the Solver.} *)
module type S = sig
  type t
  (** State of the theory *)

  type formula
  (** The type of formulas. Should be compatble with Formula_intf.S *)

  type proof
  (** A custom type for the proofs of lemmas produced by the theory. *)

  module Form : sig
    type t = formula
    (** The type of atomic formulas. *)

    val equal : t -> t -> bool
    (** Equality over formulas. *)

    val hash : t -> int
    (** Hashing function for formulas. Should be such that two formulas equal according
        to {!val:Expr_intf.S.equal} have the same hash. *)

    val print : Format.formatter -> t -> unit
    (** Printing function used among other thing for debugging.  *)

    val dummy : t
    (** Formula constant. A valid formula should never be physically equal to [dummy] *)

    val neg : t -> t
    (** Formula negation. Should be an involution, i.e. [equal a (neg neg a)] should
        always hold. *)

    val norm : t -> t * negated
    (** Returns a 'normalized' form of the formula, possibly negated
        (in which case return [Negated]). This function is used to recognize
        the link between a formula [a] and its negation [neg a], so the goal is
        that [a] and [neg a] normalise to the same formula,
        but one returns [Same_sign] and the other one returns [Negated] *)
  end

  val create : (formula, proof) actions -> t
  (** Create a new instance of the theory *)

  val assume : t -> (formula, proof) slice_actions -> (formula, proof) res
  (** Assume the formulas in the slice, possibly pushing new formulas to be propagated,
      and returns the result of the new assumptions. *)

  val if_sat : t -> (formula, proof) slice_actions -> (formula, proof) res
  (** Called at the end of the search in case a model has been found. If no new clause is
      pushed, then 'sat' is returned, else search is resumed. *)
end

