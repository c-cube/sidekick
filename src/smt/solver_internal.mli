(** A view of the solver from a theory's point of view.

    Theories should interact with the solver via this module, to assert
    new lemmas, propagate literals, access the congruence closure, etc. *)

open Sigs

type t
(** Main type for the SMT solver *)

type solver = t

val tst : t -> term_store
val stats : t -> Stat.t

val proof : t -> proof_trace
(** Access the proof object *)

val registry : t -> Registry.t
(** A solver contains a registry so that theories can share data *)

(** {3 Actions for the theories} *)

type theory_actions
(** Handle that the theories can use to perform actions. *)

(** {3 Congruence Closure} *)

val cc : t -> CC.t
(** Congruence closure for this solver *)

(** {3 Backtracking} *)

include Sidekick_sigs.BACKTRACKABLE0 with type t := t

(** {3 Interface to SAT} *)

val to_sat_plugin : t -> (module Sidekick_sat.PLUGIN)

(** {3 Simplifiers} *)

type simplify_hook = Simplify.hook

val simplifier : t -> Simplify.t

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

module type PREPROCESS_ACTS = Preprocess.PREPROCESS_ACTS

type preprocess_actions = (module PREPROCESS_ACTS)
(** Actions available to the preprocessor *)

type preprocess_hook =
  Preprocess.t ->
  is_sub:bool ->
  recurse:(term -> term) ->
  preprocess_actions ->
  term ->
  term option
(** Given a term, preprocess it.

      The idea is to add literals and clauses to help define the meaning of
      the term, if needed. For example for boolean formulas, clauses
      for their Tseitin encoding can be added, with the formula acting
      as its own proxy symbol.

      @param preprocess_actions actions available during preprocessing.
  *)

val preprocess : t -> Preprocess.t

val on_preprocess : t -> preprocess_hook -> unit
(** Add a hook that will be called when terms are preprocessed *)

val preprocess_clause : t -> lit list -> step_id -> lit list * step_id
val preprocess_clause_array : t -> lit array -> step_id -> lit array * step_id

val simplify_and_preproc_lit : t -> lit -> lit * step_id option
(** Simplify literal then preprocess it *)

(** {3 Finding foreign variables} *)

val find_foreign : t -> Find_foreign.t

val on_find_foreign : t -> Find_foreign.hook -> unit
(** Add a hook for finding foreign variables *)

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

val add_ty : t -> ty:term -> unit
(** Declare a sort for the SMT solver *)

val mk_lit : t -> ?sign:bool -> term -> lit
(** Create a literal. This automatically preprocesses the term. *)

val add_lit : t -> theory_actions -> ?default_pol:bool -> lit -> unit
(** Add the given literal to the SAT solver, so it gets assigned
      a boolean value.
      @param default_pol default polarity for the corresponding atom *)

val add_lit_t : t -> theory_actions -> ?sign:bool -> term -> unit
(** Add the given (signed) bool term to the SAT solver, so it gets assigned
      a boolean value *)

val cc_find : t -> E_node.t -> E_node.t
(** Find representative of the node *)

val cc_are_equal : t -> term -> term -> bool
(** Are these two terms equal in the congruence closure? *)

val cc_resolve_expl : t -> CC_expl.t -> lit list * step_id

(*
  val cc_raise_conflict_expl : t -> theory_actions -> CC_expl.t -> 'a
  (** Raise a conflict with the given congruence closure explanation.
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val cc_merge :
    t -> theory_actions -> E_node.t -> E_node.t -> CC_expl.t -> unit
  (** Merge these two nodes in the congruence closure, given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val cc_merge_t : t -> theory_actions -> term -> term -> CC_expl.t -> unit
  (** Merge these two terms in the congruence closure, given this explanation.
      See {!cc_merge} *)
  *)

val cc_add_term : t -> term -> E_node.t
(** Add/retrieve congruence closure node for this term.
      To be used in theories *)

val cc_mem_term : t -> term -> bool
(** Return [true] if the term is explicitly in the congruence closure.
      To be used in theories *)

val on_cc_pre_merge :
  t ->
  (CC.t * E_node.t * E_node.t * CC_expl.t -> CC.Handler_action.or_conflict) ->
  unit
(** Callback for when two classes containing data for this key are merged (called before) *)

val on_cc_post_merge :
  t -> (CC.t * E_node.t * E_node.t -> CC.Handler_action.t list) -> unit
(** Callback for when two classes containing data for this key are merged (called after)*)

val on_cc_new_term :
  t -> (CC.t * E_node.t * term -> CC.Handler_action.t list) -> unit
(** Callback to add data on terms when they are added to the congruence
      closure *)

val on_cc_is_subterm :
  t -> (CC.t * E_node.t * term -> CC.Handler_action.t list) -> unit
(** Callback for when a term is a subterm of another term in the
      congruence closure *)

val on_cc_conflict : t -> (CC.ev_on_conflict -> unit) -> unit
(** Callback called on every CC conflict *)

val on_cc_propagate :
  t ->
  (CC.t * lit * (unit -> lit list * step_id) -> CC.Handler_action.t list) ->
  unit
(** Callback called on every CC propagation *)

val on_new_ty : t -> (ty, unit) Event.t
(** Add a callback for when new types are added via {!add_ty} *)

val on_partial_check : t -> (t -> theory_actions -> lit Iter.t -> unit) -> unit
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

val declare_pb_is_incomplete : t -> unit
(** Declare that, in some theory, the problem is outside the logic fragment
      that is decidable (e.g. if we meet proper NIA formulas).
      The solver will not reply "SAT" from now on. *)

(** {3 Model production} *)

type model_ask_hook =
  t -> Model_builder.t -> Term.t -> (value * Term.t list) option
(** A model-production hook to query values from a theory.

    It takes the solver, a class, and returns an optional value for this class
    (potentially with sub-terms to find values for, if the value is actually a
    skeleton).

    For example, an arithmetic theory might detect that a class contains a
    numeric constant, and return this constant as a model value. The theory
    of arrays might return [array.const $v] for an array [Array A B],
    where [$v] will be picked by the theory of the sort [B].

    If no hook assigns a value to a class, a fake value is created for it.
*)

type model_completion_hook = t -> add:(term -> value -> unit) -> unit
(** A model production hook, for the theory to add values.
    The hook is given a [add] function to add bindings to the model. *)

val on_model :
  ?ask:model_ask_hook -> ?complete:model_completion_hook -> t -> unit
(** Add model production/completion hooks. *)

val on_progress : t -> (unit, unit) Event.t

val is_complete : t -> bool
(** Are we still in a complete logic fragment? *)

val last_model : t -> Model.t option

(** {2 Delayed actions} *)

module type PERFORM_ACTS = sig
  type t

  val add_clause : solver -> t -> keep:bool -> lit list -> step_id -> unit
  val add_lit : solver -> t -> ?default_pol:bool -> lit -> unit
end

module Perform_delayed (A : PERFORM_ACTS) : sig
  val top : t -> A.t -> unit
end

val add_theory_state :
  st:'a ->
  push_level:('a -> unit) ->
  pop_levels:('a -> int -> unit) ->
  t ->
  unit

val create :
  (module ARG) -> stat:Stat.t -> proof:Proof_trace.t -> Term.store -> unit -> t
