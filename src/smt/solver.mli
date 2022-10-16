(** Main solver type, user facing.

    This is the solver a user of sidekick can see, after instantiating
    everything. The user can add some theories, clauses, etc. and asks
    the solver to check satisfiability.

    Theory implementors will mostly interact with {!SOLVER_INTERNAL}. *)

open Sigs
module Check_res = Sidekick_abstract_solver.Check_res
module Unknown = Sidekick_abstract_solver.Unknown

type t
(** The solver's state. *)

val registry : t -> Registry.t
(** A solver contains a registry so that theories can share data *)

type theory = Theory.t

val mk_theory :
  name:string ->
  create_and_setup:(id:Theory_id.t -> Solver_internal.t -> 'th) ->
  ?push_level:('th -> unit) ->
  ?pop_levels:('th -> int -> unit) ->
  unit ->
  Theory.t
(** Helper to create a theory. *)

(** {3 Main API} *)

val stats : t -> Stat.t
val tst : t -> Term.store
val tracer : t -> Tracer.t

val create :
  (module ARG) ->
  ?stat:Stat.t ->
  ?size:[ `Big | `Tiny | `Small ] ->
  (* TODO? ?config:Config.t -> *)
  tracer:Tracer.t ->
  theories:Theory.t list ->
  Term.store ->
  unit ->
  t
(** Create a new solver.

      It needs a term state and a type state to manipulate terms and types.
      All terms and types interacting with this solver will need to come
      from these exact states.

      @param store_proof if true, proofs from the SAT solver and theories
      are retained and potentially accessible after {!solve}
      returns UNSAT.
      @param size influences the size of initial allocations.
      @param theories theories to load from the start. Other theories
      can be added using {!add_theory}. *)

val create_default :
  ?stat:Stat.t ->
  ?size:[ `Big | `Tiny | `Small ] ->
  (* TODO? ?config:Config.t -> *)
  tracer:Tracer.t ->
  theories:Theory.t list ->
  Term.store ->
  unit ->
  t
(** Create a new solver with the default CC view, and where all boolean subterms
    are mapped to boolean atoms. *)

val add_theory : t -> Theory.t -> unit
(** Add a theory to the solver. This should be called before
      any call to {!solve} or to {!add_clause} and the likes (otherwise
      the theory will have a partial view of the problem). *)

val add_theory_p : t -> 'a Theory.p -> 'a
(** Add the given theory and obtain its state *)

val add_theory_l : t -> Theory.t list -> unit

val mk_lit_t : t -> ?sign:bool -> term -> lit
(** [mk_lit_t _ ~sign t] returns [lit'],
      where [lit'] is [preprocess(lit)] and [lit] is
      an internal representation of [± t].

      The proof of [|- lit = lit'] is directly added to the solver's proof. *)

val add_clause : t -> lit array -> Proof.Pterm.delayed -> unit
(** [add_clause solver cs] adds a boolean clause to the solver.
    Subsequent calls to {!solve} will need to satisfy this clause. *)

val add_clause_l : t -> lit list -> Proof.Pterm.delayed -> unit
(** Add a clause to the solver, given as a list. *)

val assert_terms : t -> term list -> unit
(** Helper that turns each term into an atom, before adding disjunction of
    the resulting atoms to the solver as a clause assertion *)

val assert_term : t -> term -> unit
(** Helper that turns the term into an atom, before adding the result
    to the solver as a unit clause assertion *)

val add_ty : t -> ty -> unit

type value = Term.t

type sat_result = Check_res.sat_result = {
  get_value: Term.t -> value option;  (** Value for this term *)
  iter_classes: (Term.t Iter.t * value) Iter.t;
      (** All equivalence classes in the congruence closure *)
  eval_lit: Lit.t -> bool option;  (** Evaluate literal *)
  iter_true_lits: Lit.t Iter.t;
      (** Iterate on literals that are true in the trail *)
}
(** Satisfiable *)

type unsat_result = Check_res.unsat_result = {
  unsat_core: unit -> Lit.t Iter.t;
      (** Unsat core (subset of assumptions), or empty *)
  unsat_proof: unit -> Sidekick_proof.Step.id option;
      (** Proof step for the empty clause *)
}
(** Unsatisfiable *)

(** Result of solving for the current set of clauses *)
type res = Check_res.t =
  | Sat of sat_result
  | Unsat of unsat_result
  | Unknown of Unknown.t
      (** Unknown, obtained after a timeout, memory limit, etc. *)

(* TODO: API to push/pop/clear assumptions, in addition to ~assumptions param *)

val solve :
  ?on_exit:(unit -> unit) list ->
  ?on_progress:(unit -> unit) ->
  ?should_stop:(int -> bool) ->
  assumptions:lit list ->
  t ->
  res
(** [solve s] checks the satisfiability of the clauses added so far to [s].
      @param on_progress called regularly during solving.
      @param assumptions a set of atoms held to be true. The unsat core,
        if any, will be a subset of [assumptions].
      @param should_stop a callback regularly called from within the solver.
        It is given a number of "steps" done since last call. The exact notion
        of step is not defined, but is guaranteed to increase regularly.
        The function should return [true] if it judges solving
        must stop (returning [Unknown]), [false] if solving can proceed.
      @param on_exit functions to be run before this returns *)

val as_asolver : t -> Sidekick_abstract_solver.Asolver.t
(** Comply to the abstract solver interface *)

val last_res : t -> res option
(** Last result, if any. Some operations will erase this (e.g. {!assert_term}). *)

val push_assumption : t -> lit -> unit
(** Pushes an assumption onto the assumption stack. It will remain
      there until it's pop'd by {!pop_assumptions}. *)

val pop_assumptions : t -> int -> unit
(** [pop_assumptions solver n] removes [n] assumptions from the stack.
      It removes the assumptions that were the most
      recently added via {!push_assumptions}.
      Note that {!check_sat_propagations_only} can call this if it meets
      a conflict. *)

type propagation_result =
  | PR_sat
  | PR_conflict of { backtracked: int }
  | PR_unsat of { unsat_core: unit -> lit Iter.t }

val check_sat_propagations_only :
  assumptions:lit list -> t -> propagation_result
(** [check_sat_propagations_only solver] uses assumptions (including
      the [assumptions] parameter, and atoms previously added via {!push_assumptions})
      and boolean+theory propagation to quickly assess satisfiability.
      It is not complete; calling {!solve} is required to get an accurate
      result.
      @returns one of:

      - [PR_sat] if the current state seems satisfiable
      - [PR_conflict {backtracked=n}] if a conflict was found and resolved,
      leading to backtracking [n] levels of assumptions
      - [PR_unsat …] if the assumptions were found to be unsatisfiable, with
        the given core.
  *)

val pp_stats : t CCFormat.printer
(** Print some statistics. What it prints exactly is unspecified. *)
