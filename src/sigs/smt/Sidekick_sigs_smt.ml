(** Signature for the main SMT solver types.

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
    - a bridge to some SAT solver

    In this module we collect signatures defined elsewhere and define
    the module types for the main SMT solver.
*)

module type TERM = Sidekick_sigs_term.S
module type LIT = Sidekick_sigs_lit.S
module type PROOF_TRACE = Sidekick_sigs_proof_trace.S

module type SAT_PROOF_RULES = Sidekick_sigs_proof_sat.S
(** Signature for SAT-solver proof emission. *)

module type PROOF_CORE = Sidekick_sigs_proof_core.S
(** Proofs of unsatisfiability. *)

(** Registry to extract values *)
module type REGISTRY = sig
  type t
  type 'a key

  val create_key : unit -> 'a key
  (** Call this statically, typically at program initialization, for
      each distinct key. *)

  val create : unit -> t
  val get : t -> 'a key -> 'a option
  val set : t -> 'a key -> 'a -> unit
end

(** A view of the solver from a theory's point of view.

    Theories should interact with the solver via this module, to assert
    new lemmas, propagate literals, access the congruence closure, etc. *)
module type SOLVER_INTERNAL = sig
  module T : TERM
  module Lit : LIT with module T = T
  module Proof_trace : PROOF_TRACE

  type ty = T.Ty.t
  type term = T.Term.t
  type value = T.Term.t
  type lit = Lit.t
  type term_store = T.Term.store
  type ty_store = T.Ty.store
  type clause_pool
  type proof_trace = Proof_trace.t
  type step_id = Proof_trace.A.step_id

  type t
  (** {3 Main type for a solver} *)

  type solver = t

  val tst : t -> term_store
  val ty_st : t -> ty_store
  val stats : t -> Stat.t

  val proof : t -> proof_trace
  (** Access the proof object *)

  (** {3 Registry} *)

  module Registry : REGISTRY

  val registry : t -> Registry.t
  (** A solver contains a registry so that theories can share data *)

  (** {3 Exported Proof rules} *)

  module P_core_rules :
    Sidekick_sigs_proof_core.S
      with type rule = Proof_trace.A.rule
       and type step_id = Proof_trace.A.step_id
       and type term = term
       and type lit = lit

  (** {3 Actions for the theories} *)

  type theory_actions
  (** Handle that the theories can use to perform actions. *)

  (** {3 Congruence Closure} *)

  (** Congruence closure instance *)
  module CC :
    Sidekick_sigs_cc.S
      with module T = T
       and module Lit = Lit
       and module Proof_trace = Proof_trace

  val cc : t -> CC.t
  (** Congruence closure for this solver *)

  (** {3 Simplifiers} *)

  (* TODO: move into its own library *)

  (** Simplify terms *)
  module Simplify : sig
    type t

    val tst : t -> term_store
    val ty_st : t -> ty_store

    val clear : t -> unit
    (** Reset internal cache, etc. *)

    val proof : t -> proof_trace
    (** Access proof *)

    type hook = t -> term -> (term * step_id Iter.t) option
    (** Given a term, try to simplify it. Return [None] if it didn't change.

        A simple example could be a hook that takes a term [t],
        and if [t] is [app "+" (const x) (const y)] where [x] and [y] are number,
        returns [Some (const (x+y))], and [None] otherwise.

        The simplifier will take care of simplifying the resulting term further,
        caching (so that work is not duplicated in subterms), etc.
    *)

    val normalize : t -> term -> (term * step_id) option
    (** Normalize a term using all the hooks. This performs
        a fixpoint, i.e. it only stops when no hook applies anywhere inside
        the term. *)

    val normalize_t : t -> term -> term * step_id option
    (** Normalize a term using all the hooks, along with a proof that the
        simplification is correct.
        returns [t, ø] if no simplification occurred. *)
  end

  type simplify_hook = Simplify.hook

  val add_simplifier : t -> Simplify.hook -> unit
  (** Add a simplifier hook for preprocessing. *)

  val simplify_t : t -> term -> (term * step_id) option
  (** Simplify input term, returns [Some u] if some
      simplification occurred. *)

  val simp_t : t -> term -> term * step_id option
  (** [simp_t si t] returns [u] even if no simplification occurred
      (in which case [t == u] syntactically).
      It emits [|- t=u].
      (see {!simplifier}) *)

  (** {3 Preprocessors}
      These preprocessors turn mixed, raw literals (possibly simplified) into
      literals suitable for reasoning.
      Typically some clauses are also added to the solver. *)

  (* TODO: move into its own sig + library *)
  module type PREPROCESS_ACTS = sig
    val proof : proof_trace

    val mk_lit : ?sign:bool -> term -> lit
    (** [mk_lit t] creates a new literal for a boolean term [t]. *)

    val add_clause : lit list -> step_id -> unit
    (** pushes a new clause into the SAT solver. *)

    val add_lit : ?default_pol:bool -> lit -> unit
    (** Ensure the literal will be decided/handled by the SAT solver. *)
  end

  type preprocess_actions = (module PREPROCESS_ACTS)
  (** Actions available to the preprocessor *)

  type preprocess_hook = t -> preprocess_actions -> term -> unit
  (** Given a term, preprocess it.

      The idea is to add literals and clauses to help define the meaning of
      the term, if needed. For example for boolean formulas, clauses
      for their Tseitin encoding can be added, with the formula acting
      as its own proxy symbol.

      @param preprocess_actions actions available during preprocessing.
  *)

  val on_preprocess : t -> preprocess_hook -> unit
  (** Add a hook that will be called when terms are preprocessed *)

  (** {3 hooks for the theory} *)

  val raise_conflict : t -> theory_actions -> lit list -> step_id -> 'a
  (** Give a conflict clause to the solver *)

  val push_decision : t -> theory_actions -> lit -> unit
  (** Ask the SAT solver to decide the given literal in an extension of the
      current trail. This is useful for theory combination.
      If the SAT solver backtracks, this (potential) decision is removed
      and forgotten. *)

  val propagate :
    t -> theory_actions -> lit -> reason:(unit -> lit list * step_id) -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val propagate_l : t -> theory_actions -> lit -> lit list -> step_id -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val add_clause_temp : t -> theory_actions -> lit list -> step_id -> unit
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  val add_clause_permanent : t -> theory_actions -> lit list -> step_id -> unit
  (** Add toplevel clause to the SAT solver. This clause will
      not be backtracked. *)

  val mk_lit : t -> theory_actions -> ?sign:bool -> term -> lit
  (** Create a literal. This automatically preprocesses the term. *)

  val add_lit : t -> theory_actions -> ?default_pol:bool -> lit -> unit
  (** Add the given literal to the SAT solver, so it gets assigned
      a boolean value.
      @param default_pol default polarity for the corresponding atom *)

  val add_lit_t : t -> theory_actions -> ?sign:bool -> term -> unit
  (** Add the given (signed) bool term to the SAT solver, so it gets assigned
      a boolean value *)

  val cc_find : t -> CC.E_node.t -> CC.E_node.t
  (** Find representative of the node *)

  val cc_are_equal : t -> term -> term -> bool
  (** Are these two terms equal in the congruence closure? *)

  val cc_resolve_expl : t -> CC.Expl.t -> lit list * step_id

  (*
  val cc_raise_conflict_expl : t -> theory_actions -> CC.Expl.t -> 'a
  (** Raise a conflict with the given congruence closure explanation.
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val cc_merge :
    t -> theory_actions -> CC.E_node.t -> CC.E_node.t -> CC.Expl.t -> unit
  (** Merge these two nodes in the congruence closure, given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val cc_merge_t : t -> theory_actions -> term -> term -> CC.Expl.t -> unit
  (** Merge these two terms in the congruence closure, given this explanation.
      See {!cc_merge} *)
  *)

  val cc_add_term : t -> term -> CC.E_node.t
  (** Add/retrieve congruence closure node for this term.
      To be used in theories *)

  val cc_mem_term : t -> term -> bool
  (** Return [true] if the term is explicitly in the congruence closure.
      To be used in theories *)

  val on_cc_pre_merge :
    t ->
    (CC.t * CC.E_node.t * CC.E_node.t * CC.Expl.t ->
    CC.Handler_action.or_conflict) ->
    unit
  (** Callback for when two classes containing data for this key are merged (called before) *)

  val on_cc_post_merge :
    t -> (CC.t * CC.E_node.t * CC.E_node.t -> CC.Handler_action.t list) -> unit
  (** Callback for when two classes containing data for this key are merged (called after)*)

  val on_cc_new_term :
    t -> (CC.t * CC.E_node.t * term -> CC.Handler_action.t list) -> unit
  (** Callback to add data on terms when they are added to the congruence
      closure *)

  val on_cc_is_subterm :
    t -> (CC.t * CC.E_node.t * term -> CC.Handler_action.t list) -> unit
  (** Callback for when a term is a subterm of another term in the
      congruence closure *)

  val on_cc_conflict : t -> (CC.ev_on_conflict -> unit) -> unit
  (** Callback called on every CC conflict *)

  val on_cc_propagate :
    t ->
    (CC.t * lit * (unit -> lit list * step_id) -> CC.Handler_action.t list) ->
    unit
  (** Callback called on every CC propagation *)

  val on_partial_check :
    t -> (t -> theory_actions -> lit Iter.t -> unit) -> unit
  (** Register callbacked to be called with the slice of literals
      newly added on the trail.

      This is called very often and should be efficient. It doesn't have
      to be complete, only correct. It's given only the slice of
      the trail consisting in new literals. *)

  val on_final_check : t -> (t -> theory_actions -> lit Iter.t -> unit) -> unit
  (** Register callback to be called during the final check.

      Must be complete (i.e. must raise a conflict if the set of literals is
      not satisfiable) and can be expensive. The function
      is given the whole trail.
  *)

  val on_th_combination :
    t -> (t -> theory_actions -> (term * value) Iter.t) -> unit
  (** Add a hook called during theory combination.
      The hook must return an iterator of pairs [(t, v)]
      which mean that term [t] has value [v] in the model.

      Terms with the same value (according to {!Term.equal}) will be
      merged in the CC; if two terms with different values are merged,
      we get a semantic conflict and must pick another model. *)

  val declare_pb_is_incomplete : t -> unit
  (** Declare that, in some theory, the problem is outside the logic fragment
      that is decidable (e.g. if we meet proper NIA formulas).
      The solver will not reply "SAT" from now on. *)

  (** {3 Model production} *)

  type model_ask_hook =
    recurse:(t -> CC.E_node.t -> term) -> t -> CC.E_node.t -> term option
  (** A model-production hook to query values from a theory.

      It takes the solver, a class, and returns
      a term for this class. For example, an arithmetic theory
      might detect that a class contains a numeric constant, and return
      this constant as a model value.

      If no hook assigns a value to a class, a fake value is created for it.
  *)

  type model_completion_hook = t -> add:(term -> term -> unit) -> unit
  (** A model production hook, for the theory to add values.
      The hook is given a [add] function to add bindings to the model. *)

  val on_model :
    ?ask:model_ask_hook -> ?complete:model_completion_hook -> t -> unit
  (** Add model production/completion hooks. *)
end

(** User facing view of the solver.

    This is the solver a user of sidekick can see, after instantiating
    everything. The user can add some theories, clauses, etc. and asks
    the solver to check satisfiability.

    Theory implementors will mostly interact with {!SOLVER_INTERNAL}. *)
module type SOLVER = sig
  module T : TERM
  module Lit : LIT with module T = T
  module Proof_trace : PROOF_TRACE

  (** Internal solver, available to theories.  *)
  module Solver_internal :
    SOLVER_INTERNAL
      with module T = T
       and module Lit = Lit
       and module Proof_trace = Proof_trace

  type t
  (** The solver's state. *)

  type solver = t
  type term = T.Term.t
  type ty = T.Ty.t
  type lit = Lit.t
  type proof_trace = Proof_trace.t
  type step_id = Proof_trace.A.step_id

  (** {3 Value registry} *)

  module Registry : REGISTRY

  val registry : t -> Registry.t
  (** A solver contains a registry so that theories can share data *)

  (** {3 A theory}

      Theories are abstracted over the concrete implementation of the solver,
      so they can work with any implementation.

      Typically a theory should be a functor taking an argument containing
      a [SOLVER_INTERNAL] or even a full [SOLVER],
      and some additional views on terms, literals, etc.
      that are specific to the theory (e.g. to map terms to linear
      expressions).
      The theory can then be instantiated on any kind of solver for any
      term representation that also satisfies the additional theory-specific
      requirements. Instantiated theories (ie values of type {!SOLVER.theory})
      can be added to the solver.
  *)
  module type THEORY = sig
    type t
    (** The theory's state *)

    val name : string
    (** Name of the theory (ideally, unique and short) *)

    val create_and_setup : Solver_internal.t -> t
    (** Instantiate the theory's state for the given (internal) solver,
        register callbacks, create keys, etc.

        Called once for every solver this theory is added to. *)

    val push_level : t -> unit
    (** Push backtracking level. When the corresponding pop is called,
        the theory's state should be restored to a state {b equivalent}
        to what it was just before [push_level].

        it does not have to be exactly the same state, it just needs to
        be equivalent. *)

    val pop_levels : t -> int -> unit
    (** [pop_levels theory n] pops [n] backtracking levels,
        restoring [theory] to its state before calling [push_level] n times. *)
  end

  type theory = (module THEORY)
  (** A theory that can be used for this particular solver. *)

  type 'a theory_p = (module THEORY with type t = 'a)
  (** A theory that can be used for this particular solver, with state
      of type ['a]. *)

  val mk_theory :
    name:string ->
    create_and_setup:(Solver_internal.t -> 'th) ->
    ?push_level:('th -> unit) ->
    ?pop_levels:('th -> int -> unit) ->
    unit ->
    theory
  (** Helper to create a theory. *)

  (** Models

      A model can be produced when the solver is found to be in a
      satisfiable state after a call to {!solve}. *)
  module Model : sig
    type t

    val empty : t
    val mem : t -> term -> bool
    val find : t -> term -> term option
    val eval : t -> term -> term option
    val pp : t Fmt.printer
  end

  (* TODO *)
  module Unknown : sig
    type t

    val pp : t CCFormat.printer

    (*
    type unknown =
      | U_timeout
      | U_incomplete
       *)
  end

  (** {3 Main API} *)

  val stats : t -> Stat.t
  val tst : t -> T.Term.store
  val ty_st : t -> T.Ty.store
  val proof : t -> proof_trace

  val create :
    ?stat:Stat.t ->
    ?size:[ `Big | `Tiny | `Small ] ->
    (* TODO? ?config:Config.t -> *)
    proof:proof_trace ->
    theories:theory list ->
    T.Term.store ->
    T.Ty.store ->
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

  val add_theory : t -> theory -> unit
  (** Add a theory to the solver. This should be called before
      any call to {!solve} or to {!add_clause} and the likes (otherwise
      the theory will have a partial view of the problem). *)

  val add_theory_p : t -> 'a theory_p -> 'a
  (** Add the given theory and obtain its state *)

  val add_theory_l : t -> theory list -> unit

  val mk_lit_t : t -> ?sign:bool -> term -> lit
  (** [mk_lit_t _ ~sign t] returns [lit'],
      where [lit'] is [preprocess(lit)] and [lit] is
      an internal representation of [± t].

      The proof of [|- lit = lit'] is directly added to the solver's proof. *)

  val add_clause : t -> lit array -> step_id -> unit
  (** [add_clause solver cs] adds a boolean clause to the solver.
      Subsequent calls to {!solve} will need to satisfy this clause. *)

  val add_clause_l : t -> lit list -> step_id -> unit
  (** Add a clause to the solver, given as a list. *)

  val assert_terms : t -> term list -> unit
  (** Helper that turns each term into an atom, before adding the result
      to the solver as an assertion *)

  val assert_term : t -> term -> unit
  (** Helper that turns the term into an atom, before adding the result
      to the solver as a unit clause assertion *)

  (** Result of solving for the current set of clauses *)
  type res =
    | Sat of Model.t  (** Satisfiable *)
    | Unsat of {
        unsat_core: unit -> lit Iter.t;
            (** Unsat core (subset of assumptions), or empty *)
        unsat_step_id: unit -> step_id option;
            (** Proof step for the empty clause *)
      }  (** Unsatisfiable *)
    | Unknown of Unknown.t
        (** Unknown, obtained after a timeout, memory limit, etc. *)

  (* TODO: API to push/pop/clear assumptions, in addition to ~assumptions param *)

  val solve :
    ?on_exit:(unit -> unit) list ->
    ?check:bool ->
    ?on_progress:(t -> unit) ->
    ?should_stop:(t -> int -> bool) ->
    assumptions:lit list ->
    t ->
    res
  (** [solve s] checks the satisfiability of the clauses added so far to [s].
      @param check if true, the model is checked before returning.
      @param on_progress called regularly during solving.
      @param assumptions a set of atoms held to be true. The unsat core,
        if any, will be a subset of [assumptions].
      @param should_stop a callback regularly called with the solver,
        and with a number of "steps" done since last call. The exact notion
        of step is not defined, but is guaranteed to increase regularly.
        The function should return [true] if it judges solving
        must stop (returning [Unknown]), [false] if solving can proceed.
      @param on_exit functions to be run before this returns *)

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

  (* TODO: allow on_progress to return a bool to know whether to stop? *)

  val pp_stats : t CCFormat.printer
  (** Print some statistics. What it prints exactly is unspecified. *)
end
