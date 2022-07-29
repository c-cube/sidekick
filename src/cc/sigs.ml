(** Main types for congruence closure *)

open Sidekick_core
module View = View

(** Arguments to a congruence closure's implementation *)
module type ARG = sig
  val view_as_cc : Term.t -> (Const.t, Term.t, Term.t Iter.t) View.t
  (** View the Term.t through the lens of the congruence closure *)
end

(** Collection of input types, and types defined by the congruence closure *)
module type ARGS_CLASSES_EXPL_EVENT = sig
  (** E-node.

      An e-node is a node in the congruence closure that is contained
      in some equivalence classe).
      An equivalence class is a set of terms that are currently equal
      in the partial model built by the solver.
      The class is represented by a collection of nodes, one of which is
      distinguished and is called the "representative".

      All information pertaining to the whole equivalence class is stored
      in its representative's {!E_node.t}.

      When two classes become equal (are "merged"), one of the two
      representatives is picked as the representative of the new class.
      The new class contains the union of the two old classes' nodes.

      We also allow theories to store additional information in the
      representative. This information can be used when two classes are
      merged, to detect conflicts and solve equations à la Shostak.
  *)
  module E_node : sig
    type t
    (** An E-node.

        A value of type [t] points to a particular Term.t, but see
        {!find} to get the representative of the class. *)

    include Sidekick_sigs.PRINT with type t := t

    val term : t -> Term.t
    (** Term contained in this equivalence class.
        If [is_root n], then [Term.t n] is the class' representative Term.t. *)

    val equal : t -> t -> bool
    (** Are two classes {b physically} equal? To check for
        logical equality, use [CC.E_node.equal (CC.find cc n1) (CC.find cc n2)]
        which checks for equality of representatives. *)

    val hash : t -> int
    (** An opaque hash of this E_node.t. *)

    val is_root : t -> bool
    (** Is the E_node.t a root (ie the representative of its class)?
        See {!find} to get the root. *)

    val iter_class : t -> t Iter.t
    (** Traverse the congruence class.
        Precondition: [is_root n] (see {!find} below) *)

    val iter_parents : t -> t Iter.t
    (** Traverse the parents of the class.
        Precondition: [is_root n] (see {!find} below) *)

    (* FIXME:
       [@@alert refactor "this should be replaced with a Per_class concept"]
    *)

    type bitfield
    (** A field in the bitfield of this node. This should only be
        allocated when a theory is initialized.

        Bitfields are accessed using preallocated keys.
        See {!CC_S.allocate_bitfield}.

        All fields are initially 0, are backtracked automatically,
        and are merged automatically when classes are merged. *)
  end

  (** Explanations

      Explanations are specialized proofs, created by the congruence closure
      when asked to justify why two terms are equal. *)
  module Expl : sig
    type t

    include Sidekick_sigs.PRINT with type t := t

    val mk_merge : E_node.t -> E_node.t -> t
    (** Explanation: the nodes were explicitly merged *)

    val mk_merge_t : Term.t -> Term.t -> t
    (** Explanation: the terms were explicitly merged *)

    val mk_lit : Lit.t -> t
    (** Explanation: we merged [t] and [u] because of literal [t=u],
        or we merged [t] and [true] because of literal [t],
        or [t] and [false] because of literal [¬t] *)

    val mk_list : t list -> t
    (** Conjunction of explanations *)

    val mk_theory :
      Term.t ->
      Term.t ->
      (Term.t * Term.t * t list) list ->
      Proof_term.step_id ->
      t
    (** [mk_theory t u expl_sets pr] builds a theory explanation for
        why [|- t=u]. It depends on sub-explanations [expl_sets] which
        are tuples [ (t_i, u_i, expls_i) ] where [expls_i] are
        explanations that justify [t_i = u_i] in the current congruence closure.

        The proof [pr] is the theory lemma, of the form
        [ (t_i = u_i)_i |- t=u ].
        It is resolved against each [expls_i |- t_i=u_i] obtained from
        [expl_sets], on pivot [t_i=u_i], to obtain a proof of [Gamma |- t=u]
        where [Gamma] is a subset of the literals asserted into the congruence
        closure.

        For example for the lemma [a=b] deduced by injectivity
        from [Some a=Some b] in the theory of datatypes,
        the arguments would be
        [a, b, [Some a, Some b, mk_merge_t (Some a)(Some b)], pr]
        where [pr] is the injectivity lemma [Some a=Some b |- a=b].
    *)
  end

  (** Resolved explanations.

      The congruence closure keeps explanations for why terms are in the same
      class. However these are represented in a compact, cheap form.
      To use these explanations we need to {b resolve} them into a
      resolved explanation, typically a list of
      literals that are true in the current trail and are responsible for
      merges.

      However, we can also have merged classes because they have the same value
      in the current model. *)
  module Resolved_expl : sig
    type t = { lits: Lit.t list; pr: Proof_trace.t -> Proof_term.step_id }

    include Sidekick_sigs.PRINT with type t := t
  end

  (** Per-node data *)

  type e_node = E_node.t
  (** A node of the congruence closure *)

  type repr = E_node.t
  (** Node that is currently a representative. *)

  type explanation = Expl.t
end

(** Main congruence closure signature.

    The congruence closure handles the theory QF_UF (uninterpreted
    function symbols).
    It is also responsible for {i theory combination}, and provides
    a general framework for equality reasoning that other
    theories piggyback on.

    For example, the theory of datatypes relies on the congruence closure
    to do most of the work, and "only" adds injectivity/disjointness/acyclicity
    lemmas when needed.

    Similarly, a theory of arrays would hook into the congruence closure and
    assert (dis)equalities as needed.
*)
module type S = sig
  include ARGS_CLASSES_EXPL_EVENT

  type t
  (** The congruence closure object.
      It contains a fair amount of state and is mutable
      and backtrackable. *)

  (** {3 Accessors} *)

  val term_store : t -> Term.store
  val proof : t -> Proof_trace.t

  val find : t -> e_node -> repr
  (** Current representative *)

  val add_term : t -> Term.t -> e_node
  (** Add the Term.t to the congruence closure, if not present already.
      Will be backtracked. *)

  val mem_term : t -> Term.t -> bool
  (** Returns [true] if the Term.t is explicitly present in the congruence closure *)

  val allocate_bitfield : t -> descr:string -> E_node.bitfield
  (** Allocate a new e_node field (see {!E_node.bitfield}).

      This field descriptor is henceforth reserved for all nodes
      in this congruence closure, and can be set using {!set_bitfield}
      for each class_ individually.
      This can be used to efficiently store some metadata on nodes
      (e.g. "is there a numeric value in the class"
      or "is there a constructor Term.t in the class").

      There may be restrictions on how many distinct fields are allocated
      for a given congruence closure (e.g. at most {!Sys.int_size} fields).
  *)

  val get_bitfield : t -> E_node.bitfield -> E_node.t -> bool
  (** Access the bit field of the given e_node *)

  val set_bitfield : t -> E_node.bitfield -> bool -> E_node.t -> unit
  (** Set the bitfield for the e_node. This will be backtracked.
      See {!E_node.bitfield}. *)

  type propagation_reason = unit -> Lit.t list * Proof_term.step_id

  (** Handler Actions

      Actions that can be scheduled by event handlers. *)
  module Handler_action : sig
    type t =
      | Act_merge of E_node.t * E_node.t * Expl.t
      | Act_propagate of Lit.t * propagation_reason

    (* TODO:
       - an action to modify data associated with a class
    *)

    type conflict = Conflict of Expl.t [@@unboxed]

    type or_conflict = (t list, conflict) result
    (** Actions or conflict scheduled by an event handler.

      - [Ok acts] is a list of merges and propagations
      - [Error confl] is a conflict to resolve.
    *)
  end

  (** Result Actions.


    Actions returned by the congruence closure after calling {!check}. *)
  module Result_action : sig
    type t =
      | Act_propagate of { lit: Lit.t; reason: propagation_reason }
          (** [propagate (Lit.t, reason)] declares that [reason() => Lit.t]
          is a tautology.

          - [reason()] should return a list of literals that are currently true,
            as well as a proof.
          - [Lit.t] should be a literal of interest (see {!S.set_as_lit}).

          This function might never be called, a congruence closure has the right
          to not propagate and only trigger conflicts. *)

    type conflict =
      | Conflict of Lit.t list * Proof_term.step_id
          (** [raise_conflict (c,pr)] declares that [c] is a tautology of
          the theory of congruence.
          @param pr the proof of [c] being a tautology *)

    type or_conflict = (t list, conflict) result
  end

  (** {3 Events}

      Events triggered by the congruence closure, to which
      other plugins can subscribe. *)

  (** Events emitted by the congruence closure when something changes. *)
  val on_pre_merge :
    t -> (t * E_node.t * E_node.t * Expl.t, Handler_action.or_conflict) Event.t
  (** [Ev_on_pre_merge acts n1 n2 expl] is emitted right before [n1]
      and [n2] are merged with explanation [expl].  *)

  val on_pre_merge2 :
    t -> (t * E_node.t * E_node.t * Expl.t, Handler_action.or_conflict) Event.t
  (** Second phase of "on pre merge". This runs after {!on_pre_merge}
      and is used by Plugins. {b NOTE}: Plugin state might be observed as already
      changed in these handlers. *)

  val on_post_merge :
    t -> (t * E_node.t * E_node.t, Handler_action.t list) Event.t
  (** [ev_on_post_merge acts n1 n2] is emitted right after [n1]
      and [n2] were merged. [find cc n1] and [find cc n2] will return
      the same E_node.t. *)

  val on_new_term : t -> (t * E_node.t * Term.t, Handler_action.t list) Event.t
  (** [ev_on_new_term n t] is emitted whenever a new Term.t [t]
      is added to the congruence closure. Its E_node.t is [n]. *)

  type ev_on_conflict = { cc: t; th: bool; c: Lit.t list }
  (** Event emitted when a conflict occurs in the CC.

      [th] is true if the explanation for this conflict involves
      at least one "theory" explanation; i.e. some of the equations
      participating in the conflict are purely syntactic theories
      like injectivity of constructors. *)

  val on_conflict : t -> (ev_on_conflict, unit) Event.t
  (** [ev_on_conflict {th; c}] is emitted when the congruence
      closure triggers a conflict by asserting the tautology [c]. *)

  val on_propagate :
    t ->
    ( t * Lit.t * (unit -> Lit.t list * Proof_term.step_id),
      Handler_action.t list )
    Event.t
  (** [ev_on_propagate Lit.t reason] is emitted whenever [reason() => Lit.t]
      is a propagated lemma. See {!CC_ACTIONS.propagate}. *)

  val on_is_subterm :
    t -> (t * E_node.t * Term.t, Handler_action.t list) Event.t
  (** [ev_on_is_subterm n t] is emitted when [n] is a subterm of
      another E_node.t for the first time. [t] is the Term.t corresponding to
      the E_node.t [n]. This can be useful for theory combination. *)

  (** {3 Misc} *)

  val n_true : t -> E_node.t
  (** Node for [true] *)

  val n_false : t -> E_node.t
  (** Node for [false] *)

  val n_bool : t -> bool -> E_node.t
  (** Node for either true or false *)

  val set_as_lit : t -> E_node.t -> Lit.t -> unit
  (** map the given e_node to a literal. *)

  val find_t : t -> Term.t -> repr
  (** Current representative of the Term.t.
      @raise E_node.t_found if the Term.t is not already {!add}-ed. *)

  val add_iter : t -> Term.t Iter.t -> unit
  (** Add a sequence of terms to the congruence closure *)

  val all_classes : t -> repr Iter.t
  (** All current classes. This is costly, only use if there is no other solution *)

  val explain_eq : t -> E_node.t -> E_node.t -> Resolved_expl.t
  (** Explain why the two nodes are equal.
      Fails if they are not, in an unspecified way. *)

  val explain_expl : t -> Expl.t -> Resolved_expl.t
  (** Transform explanation into an actionable conflict clause *)

  (* FIXME: remove
        val raise_conflict_from_expl : t -> actions -> Expl.t -> 'a
        (** Raise a conflict with the given explanation.
            It must be a theory tautology that [expl ==> absurd].
            To be used in theories.

            This fails in an unspecified way if the explanation, once resolved,
            satisfies {!Resolved_expl.is_semantic}. *)
  *)

  val merge : t -> E_node.t -> E_node.t -> Expl.t -> unit
  (** Merge these two nodes given this explanation.
         It must be a theory tautology that [expl ==> n1 = n2].
         To be used in theories. *)

  val merge_t : t -> Term.t -> Term.t -> Expl.t -> unit
  (** Shortcut for adding + merging *)

  (** {3 Main API *)

  val assert_eq : t -> Term.t -> Term.t -> Expl.t -> unit
  (** Assert that two terms are equal, using the given explanation. *)

  val assert_lit : t -> Lit.t -> unit
  (** Given a literal, assume it in the congruence closure and propagate
      its consequences. Will be backtracked.

      Useful for the theory combination or the SAT solver's functor *)

  val assert_lits : t -> Lit.t Iter.t -> unit
  (** Addition of many literals *)

  val check : t -> Result_action.or_conflict
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the {!actions} to propagate literals, declare conflicts, etc. *)

  val push_level : t -> unit
  (** Push backtracking level *)

  val pop_levels : t -> int -> unit
  (** Restore to state [n] calls to [push_level] earlier. Used during backtracking. *)

  val get_model : t -> E_node.t Iter.t Iter.t
  (** get all the equivalence classes so they can be merged in the model *)

  val create :
    ?stat:Stat.t -> ?size:[ `Small | `Big ] -> Term.store -> Proof_trace.t -> t
  (** Create a new congruence closure.

      @param term_store used to be able to create new terms. All terms
      interacting with this congruence closure must belong in this term state
      as well.
  *)

  (**/**)

  module Debug_ : sig
    val pp : t Fmt.printer
    (** Print the whole CC *)
  end

  (**/**)
end

(* TODO: full EGG, also have a function to update the value when
   the subterms (produced in [of_term]) are updated *)

(** Data attached to the congruence closure classes.

    This helps theories keeping track of some state for each class.
    The state of a class is the monoidal combination of the state for each
    Term.t in the class (for example, the set of terms in the
    class whose head symbol is a datatype constructor). *)
module type MONOID_PLUGIN_ARG = sig
  module CC : S

  type t
  (** Some type with a monoid structure *)

  include Sidekick_sigs.PRINT with type t := t

  val name : string
  (** name of the monoid structure (short) *)

  (* FIXME: for subs, return list of e_nodes, and assume of_term already
     returned data for them. *)
  val of_term :
    CC.t -> CC.E_node.t -> Term.t -> t option * (CC.E_node.t * t) list
  (** [of_term n t], where [t] is the Term.t annotating node [n],
      must return [maybe_m, l], where:

      - [maybe_m = Some m] if [t] has monoid value [m];
        otherwise [maybe_m=None]
      - [l] is a list of [(u, m_u)] where each [u]'s Term.t
        is a direct subterm of [t]
        and [m_u] is the monoid value attached to [u].

      *)

  val merge :
    CC.t ->
    CC.E_node.t ->
    t ->
    CC.E_node.t ->
    t ->
    CC.Expl.t ->
    (t * CC.Handler_action.t list, CC.Handler_action.conflict) result
  (** Monoidal combination of two values.

      [merge cc n1 mon1 n2 mon2 expl] returns the result of merging
      monoid values [mon1] (for class [n1]) and [mon2] (for class [n2])
      when [n1] and [n2] are merged with explanation [expl].

      @return [Ok mon] if the merge is acceptable, annotating the class of [n1 ∪ n2];
      or [Error expl'] if the merge is unsatisfiable. [expl'] can then be
      used to trigger a conflict and undo the merge.
    *)
end

(** Stateful plugin holding a per-equivalence-class monoid.

    Helps keep track of monoid state per equivalence class.
    A theory might use one or more instance(s) of this to
    aggregate some theory-specific state over all terms, with
    the information of what terms are already known to be equal
    potentially saving work for the theory. *)
module type DYN_MONOID_PLUGIN = sig
  module M : MONOID_PLUGIN_ARG
  include Sidekick_sigs.DYN_BACKTRACKABLE

  val pp : unit Fmt.printer

  val mem : M.CC.E_node.t -> bool
  (** Does the CC E_node.t have a monoid value? *)

  val get : M.CC.E_node.t -> M.t option
  (** Get monoid value for this CC E_node.t, if any *)

  val iter_all : (M.CC.repr * M.t) Iter.t
end

(** Builder for a plugin.

    The builder takes a congruence closure, and instantiate the
    plugin on it. *)
module type MONOID_PLUGIN_BUILDER = sig
  module M : MONOID_PLUGIN_ARG

  module type DYN_PL_FOR_M = DYN_MONOID_PLUGIN with module M = M

  type t = (module DYN_PL_FOR_M)

  val create_and_setup : ?size:int -> M.CC.t -> t
  (** Create a new monoid state *)
end
