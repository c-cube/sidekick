(** The external interface implemented by SAT solvers. *)

(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

open Sidekick_core
open Sigs

type clause
type plugin = Sigs.plugin

type solver
(** The main solver type. *)

type store
(** Stores atoms, clauses, etc. *)

module Clause : sig
  type t = clause

  val equal : t -> t -> bool

  module Tbl : Hashtbl.S with type key = t

  val pp : store -> t Fmt.printer
  (** Print the clause *)

  val short_name : store -> t -> string
  (** Short name for a clause. Unspecified *)

  val n_atoms : store -> t -> int

  val lits_iter : store -> t -> Lit.t Iter.t
  (** Literals of a clause *)

  val lits_a : store -> t -> Lit.t array
  (** Atoms of a clause *)

  val lits_l : store -> t -> Lit.t list
  (** List of atoms of a clause *)
end

(** {2 Main Solver Type} *)

type t = solver
(** Main solver type, containing all state for solving. *)

val store : t -> store
(** Store for the solver *)

val stat : t -> Stat.t
(** Statistics *)

val tracer : t -> Tracer.t
(** Access the inner proof *)

val on_conflict : t -> (Clause.t, unit) Event.t
val on_decision : t -> (Lit.t, unit) Event.t
val on_learnt : t -> (Clause.t, unit) Event.t
val on_gc : t -> (Lit.t array, unit) Event.t

(** {2 Types} *)

(** Result type for the solver *)
type res =
  | Sat of sat_state  (** Returned when the solver reaches SAT, with a model *)
  | Unsat of clause unsat_state
      (** Returned when the solver reaches UNSAT, with a proof *)

exception UndecidedLit
(** Exception raised by the evaluating functions when a literal
      has not yet been assigned a value. *)

(** {2 Base operations} *)

val assume : t -> Lit.t list list -> unit
(** Add the list of clauses to the current set of assumptions.
      Modifies the sat solver state in place. *)

val add_clause : t -> Lit.t list -> Proof.Pterm.delayed -> unit
(** Lower level addition of clauses *)

val add_clause_a : t -> Lit.t array -> Proof.Pterm.delayed -> unit
(** Lower level addition of clauses *)

val add_input_clause : t -> Lit.t list -> unit
(** Like {!add_clause} but with the justification of being an input clause *)

val add_input_clause_a : t -> Lit.t array -> unit
(** Like {!add_clause_a} but with justification of being an input clause *)

(** {2 Solving} *)

val solve : ?on_progress:(unit -> unit) -> ?assumptions:Lit.t list -> t -> res
(** Try and solves the current set of clauses.
      @param assumptions additional atomic assumptions to be temporarily added.
        The assumptions are just used for this call to [solve], they are
        not saved in the solver's state.
      @param on_progress regularly called during solving.
        Can raise {!Resource_exhausted}
        to stop solving.

      @raise Resource_exhausted if the on_progress handler raised it to stop
  *)

(** {2 Evaluating and adding literals} *)

val add_lit : t -> ?default_pol:bool -> Lit.t -> unit
(** Ensure the SAT solver handles this particular literal, ie add
      a boolean variable for it if it's not already there. *)

val set_default_pol : t -> Lit.t -> bool -> unit
(** Set default polarity for the given boolean variable.
      Sign of the literal is ignored. *)

val true_at_level0 : t -> Lit.t -> bool
(** [true_at_level0 a] returns [true] if [a] was proved at level0, i.e.
      it must hold in all models *)

val eval_lit : t -> Lit.t -> lbool
(** Evaluate atom in current state *)

(** {2 Assumption stack} *)

val push_assumption : t -> Lit.t -> unit
(** Pushes an assumption onto the assumption stack. It will remain
      there until it's pop'd by {!pop_assumptions}. *)

val pop_assumptions : t -> int -> unit
(** [pop_assumptions solver n] removes [n] assumptions from the stack.
      It removes the assumptions that were the most
      recently added via {!push_assumptions}. *)

(** Result returned by {!check_sat_propagations_only} *)
type propagation_result =
  | PR_sat
  | PR_conflict of { backtracked: int }
  | PR_unsat of clause unsat_state

val check_sat_propagations_only :
  ?assumptions:Lit.t list -> t -> propagation_result
(** [check_sat_propagations_only solver] uses the added clauses
      and local assumptions (using {!push_assumptions} and [assumptions])
      to quickly assess whether the context is satisfiable.
      It is not complete; calling {!solve} is required to get an accurate
      result.
      @returns either [Ok()] if propagation yielded no conflict, or [Error c]
        if a conflict clause [c] was found. *)

(** {2 Initialization} *)

val plugin_cdcl_t : (module THEORY_CDCL_T) -> (module PLUGIN)

val mk_plugin_cdcl_t :
  push_level:(unit -> unit) ->
  pop_levels:(int -> unit) ->
  ?partial_check:(acts -> unit) ->
  final_check:(acts -> unit) ->
  unit ->
  (module PLUGIN)
(** Create a plugin
    @param push_level create a new backtrack level
    @param pop_levels Pop [n] levels of the plugin
    @param partial_check Assume the lits in the slice, possibly using the [slice]
      to push new lits to be propagated or to raising a conflict or to add
      new lemmas.
      @param final_check Called at the end of the search in case a model has been found.
      If no new clause is pushed, then proof search ends and "sat" is returned;
      if lemmas are added, search is resumed;
      if a conflict clause is added, search backtracks and then resumes.
   *)

val create :
  ?stat:Stat.t ->
  ?size:[ `Tiny | `Small | `Big ] ->
  tracer:#Tracer.t ->
  plugin ->
  t
(** Create new solver
      @param theory the theory
      @param the proof
      @param size the initial size of internal data structures. The bigger,
        the faster, but also the more RAM it uses. *)

val plugin_pure_sat : plugin

val create_pure_sat :
  ?stat:Stat.t ->
  ?size:[ `Tiny | `Small | `Big ] ->
  tracer:#Tracer.t ->
  unit ->
  t
