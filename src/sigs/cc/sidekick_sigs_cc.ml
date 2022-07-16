(** Main types for congruence closure *)

module View = View

module type TERM = Sidekick_sigs_term.S
module type LIT = Sidekick_sigs_lit.S
module type PROOF_TRACE = Sidekick_sigs_proof_trace.S

(** Actions provided to the congruence closure.

    The congruence closure must be able to propagate literals when
    it detects that they are true or false; it must also
    be able to create conflicts when the set of (dis)equalities
    is inconsistent *)
module type ACTIONS = sig
  type term
  type lit
  type proof
  type proof_step

  val proof : unit -> proof

  val raise_conflict : lit list -> proof_step -> 'a
  (** [raise_conflict c pr] declares that [c] is a tautology of
      the theory of congruence. This does not return (it should raise an
      exception).
      @param pr the proof of [c] being a tautology *)

  val raise_semantic_conflict : lit list -> (bool * term * term) list -> 'a
  (** [raise_semantic_conflict lits same_val] declares that
      the conjunction of all [lits] (literals true in current trail) and tuples
      [{=,≠}, t_i, u_i] implies false.

      The [{=,≠}, t_i, u_i] are pairs of terms with the same value (if [=] / true)
      or distinct value (if [≠] / false)) in the current model.

      This does not return. It should raise an exception.
  *)

  val propagate : lit -> reason:(unit -> lit list * proof_step) -> unit
  (** [propagate lit ~reason pr] declares that [reason() => lit]
      is a tautology.

      - [reason()] should return a list of literals that are currently true.
      - [lit] should be a literal of interest (see {!CC_S.set_as_lit}).

      This function might never be called, a congruence closure has the right
      to not propagate and only trigger conflicts. *)
end

(** Arguments to a congruence closure's implementation *)
module type ARG = sig
  module T : TERM
  module Lit : LIT with module T = T
  module Proof_trace : PROOF_TRACE

  (** Arguments for the congruence closure *)
  module CC : sig
    val view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) View.t
    (** View the term through the lens of the congruence closure *)

    val mk_lit_eq : ?sign:bool -> T.Term.store -> T.Term.t -> T.Term.t -> Lit.t
    (** [mk_lit_eq store t u] makes the literal [t=u] *)

    module Proof_rules :
      Sidekick_sigs_proof_core.S
        with type term = T.Term.t
         and type lit = Lit.t
         and type step_id = Proof_trace.step_id
         and type rule = Proof_trace.rule
  end
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
  (** first, some aliases. *)

  module T : TERM
  module Lit : LIT with module T = T
  module Proof_trace : PROOF_TRACE

  type term_store = T.Term.store
  type term = T.Term.t
  type value = term
  type fun_ = T.Fun.t
  type lit = Lit.t
  type proof = Proof_trace.t
  type proof_step = Proof_trace.step_id

  type actions =
    (module ACTIONS
       with type term = T.Term.t
        and type lit = Lit.t
        and type proof = proof
        and type proof_step = proof_step)
  (** Actions available to the congruence closure *)

  type t
  (** The congruence closure object.
      It contains a fair amount of state and is mutable
      and backtrackable. *)

  (** Equivalence classes.

      An equivalence class is a set of terms that are currently equal
      in the partial model built by the solver.
      The class is represented by a collection of nodes, one of which is
      distinguished and is called the "representative".

      All information pertaining to the whole equivalence class is stored
      in this representative's node.

      When two classes become equal (are "merged"), one of the two
      representatives is picked as the representative of the new class.
      The new class contains the union of the two old classes' nodes.

      We also allow theories to store additional information in the
      representative. This information can be used when two classes are
      merged, to detect conflicts and solve equations à la Shostak.
  *)
  module Class : sig
    type t
    (** An equivalent class, containing terms that are proved
        to be equal.

        A value of type [t] points to a particular term, but see
        {!find} to get the representative of the class. *)

    val term : t -> term
    (** Term contained in this equivalence class.
        If [is_root n], then [term n] is the class' representative term. *)

    val equal : t -> t -> bool
    (** Are two classes {b physically} equal? To check for
        logical equality, use [CC.Class.equal (CC.find cc n1) (CC.find cc n2)]
        which checks for equality of representatives. *)

    val hash : t -> int
    (** An opaque hash of this node. *)

    val pp : t Fmt.printer
    (** Unspecified printing of the node, for example its term,
        a unique ID, etc. *)

    val is_root : t -> bool
    (** Is the node a root (ie the representative of its class)?
        See {!find} to get the root. *)

    val iter_class : t -> t Iter.t
    (** Traverse the congruence class.
        Precondition: [is_root n] (see {!find} below) *)

    val iter_parents : t -> t Iter.t
    (** Traverse the parents of the class.
        Precondition: [is_root n] (see {!find} below) *)

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
      when asked to justify why twp terms are equal. *)
  module Expl : sig
    type t

    val pp : t Fmt.printer

    val mk_merge : Class.t -> Class.t -> t
    (** Explanation: the nodes were explicitly merged *)

    val mk_merge_t : term -> term -> t
    (** Explanation: the terms were explicitly merged *)

    val mk_lit : lit -> t
    (** Explanation: we merged [t] and [u] because of literal [t=u],
        or we merged [t] and [true] because of literal [t],
        or [t] and [false] because of literal [¬t] *)

    val mk_same_value : Class.t -> Class.t -> t

    val mk_list : t list -> t
    (** Conjunction of explanations *)

    val mk_theory :
      term -> term -> (term * term * t list) list -> proof_step -> t
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
    type t = {
      lits: lit list;
      same_value: (Class.t * Class.t) list;
      pr: proof -> proof_step;
    }

    val is_semantic : t -> bool
    (** [is_semantic expl] is [true] if there's at least one
        pair in [expl.same_value]. *)

    val pp : t Fmt.printer
  end

  type node = Class.t
  (** A node of the congruence closure *)

  type repr = Class.t
  (** Node that is currently a representative *)

  type explanation = Expl.t

  (** {3 Accessors} *)

  val term_store : t -> term_store
  val proof : t -> proof

  val find : t -> node -> repr
  (** Current representative *)

  val add_term : t -> term -> node
  (** Add the term to the congruence closure, if not present already.
      Will be backtracked. *)

  val mem_term : t -> term -> bool
  (** Returns [true] if the term is explicitly present in the congruence closure *)

  (** {3 Events}

      Events triggered by the congruence closure, to which
      other plugins can subscribe. *)

  type ev_on_pre_merge = t -> actions -> Class.t -> Class.t -> Expl.t -> unit
  (** [ev_on_pre_merge cc acts n1 n2 expl] is called right before [n1]
      and [n2] are merged with explanation [expl].  *)

  type ev_on_post_merge = t -> actions -> Class.t -> Class.t -> unit
  (** [ev_on_post_merge cc acts n1 n2] is called right after [n1]
      and [n2] were merged. [find cc n1] and [find cc n2] will return
      the same node. *)

  type ev_on_new_term = t -> Class.t -> term -> unit
  (** [ev_on_new_term cc n t] is called whenever a new term [t]
      is added to the congruence closure. Its node is [n]. *)

  type ev_on_conflict = t -> th:bool -> lit list -> unit
  (** [ev_on_conflict acts ~th c] is called when the congruence
      closure triggers a conflict by asserting the tautology [c].

      @param th true if the explanation for this conflict involves
      at least one "theory" explanation; i.e. some of the equations
      participating in the conflict are purely syntactic theories
      like injectivity of constructors. *)

  type ev_on_propagate = t -> lit -> (unit -> lit list * proof_step) -> unit
  (** [ev_on_propagate cc lit reason] is called whenever [reason() => lit]
      is a propagated lemma. See {!CC_ACTIONS.propagate}. *)

  type ev_on_is_subterm = Class.t -> term -> unit
  (** [ev_on_is_subterm n t] is called when [n] is a subterm of
      another node for the first time. [t] is the term corresponding to
      the node [n]. This can be useful for theory combination. *)

  val create :
    ?stat:Stat.t ->
    ?on_pre_merge:ev_on_pre_merge list ->
    ?on_post_merge:ev_on_post_merge list ->
    ?on_new_term:ev_on_new_term list ->
    ?on_conflict:ev_on_conflict list ->
    ?on_propagate:ev_on_propagate list ->
    ?on_is_subterm:ev_on_is_subterm list ->
    ?size:[ `Small | `Big ] ->
    term_store ->
    proof ->
    t
  (** Create a new congruence closure.

      @param term_store used to be able to create new terms. All terms
      interacting with this congruence closure must belong in this term state
      as well. *)

  val allocate_bitfield : descr:string -> t -> Class.bitfield
  (** Allocate a new node field (see {!Class.bitfield}).

      This field descriptor is henceforth reserved for all nodes
      in this congruence closure, and can be set using {!set_bitfield}
      for each node individually.
      This can be used to efficiently store some metadata on nodes
      (e.g. "is there a numeric value in the class"
      or "is there a constructor term in the class").

      There may be restrictions on how many distinct fields are allocated
      for a given congruence closure (e.g. at most {!Sys.int_size} fields).
  *)

  val get_bitfield : t -> Class.bitfield -> Class.t -> bool
  (** Access the bit field of the given node *)

  val set_bitfield : t -> Class.bitfield -> bool -> Class.t -> unit
  (** Set the bitfield for the node. This will be backtracked.
      See {!Class.bitfield}. *)

  (* TODO: remove? this is managed by the solver anyway? *)
  val on_pre_merge : t -> ev_on_pre_merge -> unit
  (** Add a function to be called when two classes are merged *)

  val on_post_merge : t -> ev_on_post_merge -> unit
  (** Add a function to be called when two classes are merged *)

  val on_new_term : t -> ev_on_new_term -> unit
  (** Add a function to be called when a new node is created *)

  val on_conflict : t -> ev_on_conflict -> unit
  (** Called when the congruence closure finds a conflict *)

  val on_propagate : t -> ev_on_propagate -> unit
  (** Called when the congruence closure propagates a literal *)

  val on_is_subterm : t -> ev_on_is_subterm -> unit
  (** Called on terms that are subterms of function symbols *)

  val set_as_lit : t -> Class.t -> lit -> unit
  (** map the given node to a literal. *)

  val find_t : t -> term -> repr
  (** Current representative of the term.
      @raise Class.t_found if the term is not already {!add}-ed. *)

  val add_iter : t -> term Iter.t -> unit
  (** Add a sequence of terms to the congruence closure *)

  val all_classes : t -> repr Iter.t
  (** All current classes. This is costly, only use if there is no other solution *)

  val assert_lit : t -> lit -> unit
  (** Given a literal, assume it in the congruence closure and propagate
      its consequences. Will be backtracked.

      Useful for the theory combination or the SAT solver's functor *)

  val assert_lits : t -> lit Iter.t -> unit
  (** Addition of many literals *)

  val explain_eq : t -> Class.t -> Class.t -> Resolved_expl.t
  (** Explain why the two nodes are equal.
      Fails if they are not, in an unspecified way. *)

  val raise_conflict_from_expl : t -> actions -> Expl.t -> 'a
  (** Raise a conflict with the given explanation.
      It must be a theory tautology that [expl ==> absurd].
      To be used in theories.

      This fails in an unspecified way if the explanation, once resolved,
      satisfies {!Resolved_expl.is_semantic}. *)

  val n_true : t -> Class.t
  (** Node for [true] *)

  val n_false : t -> Class.t
  (** Node for [false] *)

  val n_bool : t -> bool -> Class.t
  (** Node for either true or false *)

  val merge : t -> Class.t -> Class.t -> Expl.t -> unit
  (** Merge these two nodes given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val merge_t : t -> term -> term -> Expl.t -> unit
  (** Shortcut for adding + merging *)

  val set_model_value : t -> term -> value -> unit
  (** Set the value of a term in the model. *)

  val with_model_mode : t -> (unit -> 'a) -> 'a
  (** Enter model combination mode. *)

  val get_model_for_each_class : t -> (repr * Class.t Iter.t * value) Iter.t
  (** In model combination mode, obtain classes with their values. *)

  val check : t -> actions -> unit
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the {!actions} to propagate literals, declare conflicts, etc. *)

  val push_level : t -> unit
  (** Push backtracking level *)

  val pop_levels : t -> int -> unit
  (** Restore to state [n] calls to [push_level] earlier. Used during backtracking. *)

  val get_model : t -> Class.t Iter.t Iter.t
  (** get all the equivalence classes so they can be merged in the model *)

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
    term in the class (for example, the set of terms in the
    class whose head symbol is a datatype constructor). *)
module type MONOID_ARG = sig
  module CC : S

  type t
  (** Some type with a monoid structure *)

  include Sidekick_sigs.PRINT with type t := t

  val name : string
  (** name of the monoid structure (short) *)

  val of_term :
    CC.t -> CC.Class.t -> CC.term -> t option * (CC.Class.t * t) list
  (** [of_term n t], where [t] is the term annotating node [n],
      must return [maybe_m, l], where:

      - [maybe_m = Some m] if [t] has monoid value [m];
        otherwise [maybe_m=None]
      - [l] is a list of [(u, m_u)] where each [u]'s term
        is a direct subterm of [t]
        and [m_u] is the monoid value attached to [u].

      *)

  val merge :
    CC.t ->
    CC.Class.t ->
    t ->
    CC.Class.t ->
    t ->
    CC.Expl.t ->
    (t, CC.Expl.t) result
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
module type PLUGIN = sig
  module CC : S
  module M : MONOID_ARG with module CC = CC

  val push_level : unit -> unit
  (** Push backtracking point *)

  val pop_levels : int -> unit
  (** Pop [n] backtracking points *)

  val n_levels : unit -> int

  val mem : CC.Class.t -> bool
  (** Does the CC node have a monoid value? *)

  val get : CC.Class.t -> M.t option
  (** Get monoid value for this CC node, if any *)

  val iter_all : (CC.repr * M.t) Iter.t
end

(** Builder for a plugin.

    The builder takes a congruence closure, and instantiate the
    plugin on it. *)
module type PLUGIN_BUILDER = sig
  module M : MONOID_ARG

  module type PL = PLUGIN with module CC = M.CC and module M = M

  type plugin = (module PL)

  val create_and_setup : ?size:int -> M.CC.t -> plugin
  (** Create a new monoid state *)
end
