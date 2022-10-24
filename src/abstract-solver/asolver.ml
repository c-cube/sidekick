(** Abstract interface for a solver *)

open Sidekick_core
module Unknown = Unknown
module Check_res = Check_res
module Proof = Sidekick_proof

class type t =
  object
    method assert_term : Term.t -> unit
    (** Helper that turns the term into an atom, before adding the result
        to the solver as a unit clause assertion.

        This uses {!Proof_sat.sat_input_clause} to justify the assertion. *)

    method assert_clause : Lit.t array -> Proof.Pterm.delayed -> unit
    (** [add_clause solver cs] adds a boolean clause to the solver.
      Subsequent calls to {!solve} will need to satisfy this clause. *)

    method assert_clause_l : Lit.t list -> Proof.Pterm.delayed -> unit
    (** Add a clause to the solver, given as a list. *)

    method add_ty : ty:Term.t -> unit
    (** Add a new sort/atomic type. *)

    method lit_of_term : ?sign:bool -> Term.t -> Lit.t
    (** Convert a term into a simplified literal. *)

    method tst : Term.store

    method solve :
      ?on_exit:(unit -> unit) list ->
      ?on_progress:(unit -> unit) ->
      ?should_stop:(int -> bool) ->
      assumptions:Lit.t list ->
      unit ->
      Check_res.t
    (** Checks the satisfiability of the clauses added so far to the solver.
        @param assumptions a set of atoms held to be true. The unsat core,
          if any, will be a subset of [assumptions].
        @param on_progress called regularly during solving.
        @param should_stop a callback regularly called from within the solver.
          It is given a number of "steps" done since last call. The exact notion
          of step is not defined, but is guaranteed to increase regularly.
          The function should return [true] if it judges solving
          must stop (returning [Unknown]), [false] if solving can proceed.
        @param on_exit functions to be run before this returns *)

    method last_res : Check_res.t option
    (** Returns the result of the last call to {!solve}, if the logic statee
        has not changed (mostly by asserting new clauses). *)

    method proof_tracer : Proof.Tracer.t
    (** TODO: remove, use Tracer instead *)
  end

let tst (self : #t) : Term.store = self#tst
let assert_term (self : #t) t : unit = self#assert_term t
let assert_clause (self : #t) c p : unit = self#assert_clause c p
let assert_clause_l (self : #t) c p : unit = self#assert_clause_l c p
let add_ty (self : #t) ~ty : unit = self#add_ty ~ty
let lit_of_term (self : #t) ?sign t : Lit.t = self#lit_of_term ?sign t

let solve (self : #t) ?on_exit ?on_progress ?should_stop ~assumptions () :
    Check_res.t =
  self#solve ?on_exit ?on_progress ?should_stop ~assumptions ()

let last_res (self : #t) = self#last_res
let proof (self : #t) : Proof.Tracer.t = self#proof_tracer
