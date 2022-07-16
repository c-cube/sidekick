(** {1 Main Signatures}

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
    - a bridge to some SAT solver

    In this module we define most of the main signatures used
    throughout Sidekick.
*)

module Fmt = CCFormat

(** View terms through the lens of the Congruence Closure *)
module CC_view = struct
  (** A view of a term fron the point of view of the congruence closure.

      - ['f] is the type of function symbols
      - ['t] is the type of terms
      - ['ts] is the type of sequences of terms (arguments of function application)
  *)
  type ('f, 't, 'ts) t =
    | Bool of bool
    | App_fun of 'f * 'ts
    | App_ho of 't * 't
    | If of 't * 't * 't
    | Eq of 't * 't
    | Not of 't
    | Opaque of 't
  (* do not enter *)

  (** Map function over a view, one level deep.
    Each function maps over a different type, e.g. [f_t] maps over terms *)
  let map_view ~f_f ~f_t ~f_ts (v : _ t) : _ t =
    match v with
    | Bool b -> Bool b
    | App_fun (f, args) -> App_fun (f_f f, f_ts args)
    | App_ho (f, a) -> App_ho (f_t f, f_t a)
    | Not t -> Not (f_t t)
    | If (a, b, c) -> If (f_t a, f_t b, f_t c)
    | Eq (a, b) -> Eq (f_t a, f_t b)
    | Opaque t -> Opaque (f_t t)

  (** Iterate over a view, one level deep. *)
  let iter_view ~f_f ~f_t ~f_ts (v : _ t) : unit =
    match v with
    | Bool _ -> ()
    | App_fun (f, args) ->
      f_f f;
      f_ts args
    | App_ho (f, a) ->
      f_t f;
      f_t a
    | Not t -> f_t t
    | If (a, b, c) ->
      f_t a;
      f_t b;
      f_t c
    | Eq (a, b) ->
      f_t a;
      f_t b
    | Opaque t -> f_t t
end

(** Main representation of Terms and Types *)
module type TERM = sig
  (** A function symbol, like "f" or "plus" or "is_human" or "socrates" *)
  module Fun : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  (** Types

      Types should be comparable (ideally, in O(1)), and have
      at least a boolean type available. *)
  module Ty : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    type store

    val bool : store -> t
    val is_bool : t -> bool
  end

  (** Term structure.

      Terms should be {b hashconsed}, with perfect sharing.
      This allows, for example, {!Term.Tbl} and {!Term.iter_dag} to be efficient.
  *)
  module Term : sig
    type t

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val pp : t Fmt.printer

    type store
    (** A store used to create new terms. It is where the hashconsing
        table should live, along with other all-terms related store. *)

    val ty : t -> Ty.t

    val bool : store -> bool -> t
    (** build true/false *)

    val as_bool : t -> bool option
    (** [as_bool t] is [Some true] if [t] is the term [true], and similarly
        for [false]. For other terms it is [None]. *)

    val abs : store -> t -> t * bool
    (** [abs t] returns an "absolute value" for the term, along with the
        sign of [t].

        The idea is that we want to turn [not a] into [(a, false)],
        or [(a != b)] into [(a=b, false)]. For terms without a negation this
        should return [(t, true)].

        The store is passed in case a new term needs to be created. *)

    val map_shallow : store -> (t -> t) -> t -> t
    (** Map function on immediate subterms. This should not be recursive. *)

    val iter_shallow : store -> (t -> unit) -> t -> unit
    (** Iterate function on immediate subterms. This should not be recursive. *)

    val iter_dag : t -> (t -> unit) -> unit
    (** [iter_dag t f] calls [f] once on each subterm of [t], [t] included.
        It must {b not} traverse [t] as a tree, but rather as a
        perfectly shared DAG.

        For example, in:
        {[
          let x = 2 in
          let y = f x x in
          let z = g y x in
          z = z
        ]}

        the DAG has the following nodes:

        {[ n1: 2
           n2: f n1 n1
           n3: g n2 n1
           n4: = n3 n3
         ]}
    *)

    module Tbl : CCHashtbl.S with type key = t
  end
end

(** Signature for SAT-solver proof emission. *)
module type SAT_PROOF = sig
  type t
  (** The stored proof (possibly nil, possibly on disk, possibly in memory) *)

  type proof_step
  (** identifier for a proof *)

  module Step_vec : Vec_sig.BASE with type elt = proof_step
  (** A vector of steps *)

  type lit
  (** A boolean literal for the proof trace *)

  type proof_rule = t -> proof_step
  (** A proof proof_rule constructor, used to obtain proofs from theories *)

  val enabled : t -> bool
  (** Returns true if proof production is enabled *)

  val emit_input_clause : lit Iter.t -> proof_rule
  (** Emit an input clause. *)

  val emit_redundant_clause : lit Iter.t -> hyps:proof_step Iter.t -> proof_rule
  (** Emit a clause deduced by the SAT solver, redundant wrt previous clauses.
      The clause must be RUP wrt [hyps]. *)

  val emit_unsat_core : lit Iter.t -> proof_rule
  (** Produce a proof of the empty clause given this subset of the assumptions.
      FIXME: probably needs the list of proof_step that disprove the lits? *)

  val emit_unsat : proof_step -> t -> unit
  (** Signal "unsat" result at the given proof *)

  val del_clause : proof_step -> lit Iter.t -> t -> unit
  (** Forget a clause. Only useful for performance considerations. *)
end

(** Proofs of unsatisfiability. *)
module type PROOF = sig
  type t
  (** The abstract representation of a proof. A proof always proves
      a clause to be {b valid} (true in every possible interpretation
      of the problem's assertions, and the theories) *)

  type proof_step
  (** Identifier for a proof proof_rule (like a unique ID for a clause previously
      added/proved) *)

  type term
  type lit
  type proof_rule = t -> proof_step

  include
    SAT_PROOF
      with type t := t
       and type lit := lit
       and type proof_step := proof_step
       and type proof_rule := proof_rule

  val lemma_cc : lit Iter.t -> proof_rule
  (** [lemma_cc proof lits] asserts that [lits] form a tautology for the theory
      of uninterpreted functions. *)

  val define_term : term -> term -> proof_rule
  (** [define_term cst u proof] defines the new constant [cst] as being equal
      to [u].
      The result is a proof of the clause [cst = u] *)

  val proof_p1 : proof_step -> proof_step -> proof_rule
  (** [proof_p1 p1 p2], where [p1] proves the unit clause [t=u] (t:bool)
      and [p2] proves [C \/ t], is the rule that produces [C \/ u],
      i.e unit paramodulation. *)

  val proof_r1 : proof_step -> proof_step -> proof_rule
  (** [proof_r1 p1 p2], where [p1] proves the unit clause [|- t] (t:bool)
      and [p2] proves [C \/ ¬t], is the rule that produces [C \/ u],
      i.e unit resolution. *)

  val proof_res : pivot:term -> proof_step -> proof_step -> proof_rule
  (** [proof_res ~pivot p1 p2], where [p1] proves the clause [|- C \/ l]
      and [p2] proves [D \/ ¬l], where [l] is either [pivot] or [¬pivot],
      is the rule that produces [C \/ D], i.e boolean resolution. *)

  val with_defs : proof_step -> proof_step Iter.t -> proof_rule
  (** [with_defs pr defs] specifies that [pr] is valid only in
      a context where the definitions [defs] are present. *)

  val lemma_true : term -> proof_rule
  (** [lemma_true (true) p] asserts the clause [(true)] *)

  val lemma_preprocess : term -> term -> using:proof_step Iter.t -> proof_rule
  (** [lemma_preprocess t u ~using p] asserts that [t = u] is a tautology
      and that [t] has been preprocessed into [u].

      The theorem [/\_{eqn in using} eqn |- t=u] is proved using congruence
      closure, and then resolved against the clauses [using] to obtain
      a unit equality.

      From now on, [t] and [u] will be used interchangeably.
      @return a proof_rule ID for the clause [(t=u)]. *)

  val lemma_rw_clause :
    proof_step -> res:lit Iter.t -> using:proof_step Iter.t -> proof_rule
  (** [lemma_rw_clause prc ~res ~using], where [prc] is the proof of [|- c],
      uses the equations [|- p_i = q_i] from [using]
      to rewrite some literals of [c] into [res]. This is used to preprocess
      literals of a clause (using {!lemma_preprocess} individually). *)
end

(** Literals

    Literals are a pair of a boolean-sorted term, and a sign.
    Positive literals are the same as their term, and negative literals
    are the negation of their term.

    The SAT solver deals only in literals and clauses (sets of literals).
    Everything else belongs in the SMT solver. *)
module type LIT = sig
  module T : TERM
  (** Literals depend on terms *)

  type t
  (** A literal *)

  val term : t -> T.Term.t
  (** Get the (positive) term *)

  val sign : t -> bool
  (** Get the sign. A negated literal has sign [false]. *)

  val neg : t -> t
  (** Take negation of literal. [sign (neg lit) = not (sign lit)]. *)

  val abs : t -> t
  (** [abs lit] is like [lit] but always positive, i.e. [sign (abs lit) = true] *)

  val signed_term : t -> T.Term.t * bool
  (** Return the atom and the sign *)

  val atom : ?sign:bool -> T.Term.store -> T.Term.t -> t
  (** [atom store t] makes a literal out of a term, possibly normalizing
      its sign in the process.
      @param sign if provided, and [sign=false], negate the resulting lit. *)

  val norm_sign : t -> t * bool
  (** [norm_sign (+t)] is [+t, true],
      and [norm_sign (-t)] is [+t, false].
      In both cases the term is positive, and the boolean reflects the initial sign. *)

  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer
end

(** Actions provided to the congruence closure.

    The congruence closure must be able to propagate literals when
    it detects that they are true or false; it must also
    be able to create conflicts when the set of (dis)equalities
    is inconsistent *)
module type CC_ACTIONS = sig
  module T : TERM
  module Lit : LIT with module T = T

  type proof
  type proof_step

  module P :
    PROOF
      with type lit = Lit.t
       and type t = proof
       and type term = T.Term.t
       and type proof_step = proof_step

  type t
  (** An action handle. It is used by the congruence closure
      to perform the actions below. How it performs the actions
      is not specified and is solver-specific. *)

  val proof : t -> proof

  val raise_conflict : t -> Lit.t list -> proof_step -> 'a
  (** [raise_conflict acts c pr] declares that [c] is a tautology of
      the theory of congruence. This does not return (it should raise an
      exception).
      @param pr the proof of [c] being a tautology *)

  val raise_semantic_conflict :
    t -> Lit.t list -> (bool * T.Term.t * T.Term.t) list -> 'a
  (** [raise_semantic_conflict acts lits same_val] declares that
      the conjunction of all [lits] (literals true in current trail) and tuples
      [{=,≠}, t_i, u_i] implies false.

      The [{=,≠}, t_i, u_i] are pairs of terms with the same value (if [=] / true)
      or distinct value (if [≠] / false)) in the current model.

      This does not return. It should raise an exception.
  *)

  val propagate : t -> Lit.t -> reason:(unit -> Lit.t list * proof_step) -> unit
  (** [propagate acts lit ~reason pr] declares that [reason() => lit]
      is a tautology.

      - [reason()] should return a list of literals that are currently true.
      - [lit] should be a literal of interest (see {!CC_S.set_as_lit}).

      This function might never be called, a congruence closure has the right
      to not propagate and only trigger conflicts. *)
end

(** Arguments to a congruence closure's implementation *)
module type CC_ARG = sig
  module T : TERM
  module Lit : LIT with module T = T

  type proof
  type proof_step

  module P :
    PROOF
      with type lit = Lit.t
       and type t = proof
       and type term = T.Term.t
       and type proof_step = proof_step

  module Actions :
    CC_ACTIONS
      with module T = T
       and module Lit = Lit
       and type proof = proof
       and type proof_step = proof_step

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t
  (** View the term through the lens of the congruence closure *)

  val mk_lit_eq : ?sign:bool -> T.Term.store -> T.Term.t -> T.Term.t -> Lit.t
  (** [mk_lit_eq store t u] makes the literal [t=u] *)
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
module type CC_S = sig
  (** first, some aliases. *)

  module T : TERM
  module Lit : LIT with module T = T

  type proof
  type proof_step

  module P :
    PROOF
      with type lit = Lit.t
       and type t = proof
       and type proof_step = proof_step

  module Actions :
    CC_ACTIONS
      with module T = T
       and module Lit = Lit
       and type proof = proof
       and type proof_step = proof_step

  type term_store = T.Term.store
  type term = T.Term.t
  type value = term
  type fun_ = T.Fun.t
  type lit = Lit.t
  type actions = Actions.t

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
  module N : sig
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
        logical equality, use [CC.N.equal (CC.find cc n1) (CC.find cc n2)]
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
      when asked to justify why 2 terms are equal. *)
  module Expl : sig
    type t

    val pp : t Fmt.printer

    val mk_merge : N.t -> N.t -> t
    (** Explanation: the nodes were explicitly merged *)

    val mk_merge_t : term -> term -> t
    (** Explanation: the terms were explicitly merged *)

    val mk_lit : lit -> t
    (** Explanation: we merged [t] and [u] because of literal [t=u],
        or we merged [t] and [true] because of literal [t],
        or [t] and [false] because of literal [¬t] *)

    val mk_same_value : N.t -> N.t -> t

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
      same_value: (N.t * N.t) list;
      pr: proof -> proof_step;
    }

    val is_semantic : t -> bool
    (** [is_semantic expl] is [true] if there's at least one
        pair in [expl.same_value]. *)

    val pp : t Fmt.printer
  end

  type node = N.t
  (** A node of the congruence closure *)

  type repr = N.t
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

  type ev_on_pre_merge = t -> actions -> N.t -> N.t -> Expl.t -> unit
  (** [ev_on_pre_merge cc acts n1 n2 expl] is called right before [n1]
      and [n2] are merged with explanation [expl].  *)

  type ev_on_post_merge = t -> actions -> N.t -> N.t -> unit
  (** [ev_on_post_merge cc acts n1 n2] is called right after [n1]
      and [n2] were merged. [find cc n1] and [find cc n2] will return
      the same node. *)

  type ev_on_new_term = t -> N.t -> term -> unit
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

  type ev_on_is_subterm = N.t -> term -> unit
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

  val allocate_bitfield : descr:string -> t -> N.bitfield
  (** Allocate a new node field (see {!N.bitfield}).

      This field descriptor is henceforth reserved for all nodes
      in this congruence closure, and can be set using {!set_bitfield}
      for each node individually.
      This can be used to efficiently store some metadata on nodes
      (e.g. "is there a numeric value in the class"
      or "is there a constructor term in the class").

      There may be restrictions on how many distinct fields are allocated
      for a given congruence closure (e.g. at most {!Sys.int_size} fields).
  *)

  val get_bitfield : t -> N.bitfield -> N.t -> bool
  (** Access the bit field of the given node *)

  val set_bitfield : t -> N.bitfield -> bool -> N.t -> unit
  (** Set the bitfield for the node. This will be backtracked.
      See {!N.bitfield}. *)

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

  val set_as_lit : t -> N.t -> lit -> unit
  (** map the given node to a literal. *)

  val find_t : t -> term -> repr
  (** Current representative of the term.
      @raise Not_found if the term is not already {!add}-ed. *)

  val add_seq : t -> term Iter.t -> unit
  (** Add a sequence of terms to the congruence closure *)

  val all_classes : t -> repr Iter.t
  (** All current classes. This is costly, only use if there is no other solution *)

  val assert_lit : t -> lit -> unit
  (** Given a literal, assume it in the congruence closure and propagate
      its consequences. Will be backtracked.

      Useful for the theory combination or the SAT solver's functor *)

  val assert_lits : t -> lit Iter.t -> unit
  (** Addition of many literals *)

  val explain_eq : t -> N.t -> N.t -> Resolved_expl.t
  (** Explain why the two nodes are equal.
      Fails if they are not, in an unspecified way. *)

  val raise_conflict_from_expl : t -> actions -> Expl.t -> 'a
  (** Raise a conflict with the given explanation.
      It must be a theory tautology that [expl ==> absurd].
      To be used in theories.

      This fails in an unspecified way if the explanation, once resolved,
      satisfies {!Resolved_expl.is_semantic}. *)

  val n_true : t -> N.t
  (** Node for [true] *)

  val n_false : t -> N.t
  (** Node for [false] *)

  val n_bool : t -> bool -> N.t
  (** Node for either true or false *)

  val merge : t -> N.t -> N.t -> Expl.t -> unit
  (** Merge these two nodes given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val merge_t : t -> term -> term -> Expl.t -> unit
  (** Shortcut for adding + merging *)

  val set_model_value : t -> term -> value -> unit
  (** Set the value of a term in the model. *)

  val with_model_mode : t -> (unit -> 'a) -> 'a
  (** Enter model combination mode. *)

  val get_model_for_each_class : t -> (repr * N.t Iter.t * value) Iter.t
  (** In model combination mode, obtain classes with their values. *)

  val check : t -> actions -> unit
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the {!actions} to propagate literals, declare conflicts, etc. *)

  val push_level : t -> unit
  (** Push backtracking level *)

  val pop_levels : t -> int -> unit
  (** Restore to state [n] calls to [push_level] earlier. Used during backtracking. *)

  val get_model : t -> N.t Iter.t Iter.t
  (** get all the equivalence classes so they can be merged in the model *)

  (**/**)

  module Debug_ : sig
    val pp : t Fmt.printer
  end

  (**/**)
end

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

  type ty = T.Ty.t
  type term = T.Term.t
  type value = T.Term.t
  type term_store = T.Term.store
  type ty_store = T.Ty.store
  type clause_pool
  type proof
  type proof_step

  (** {3 Proofs} *)
  module P :
    PROOF
      with type lit = Lit.t
       and type term = term
       and type t = proof
       and type proof_step = proof_step

  type t
  (** {3 Main type for a solver} *)

  type solver = t

  val tst : t -> term_store
  val ty_st : t -> ty_store
  val stats : t -> Stat.t

  val proof : t -> proof
  (** Access the proof object *)

  (** {3 Registry} *)

  module Registry : REGISTRY

  val registry : t -> Registry.t
  (** A solver contains a registry so that theories can share data *)

  (** {3 Actions for the theories} *)

  type theory_actions
  (** Handle that the theories can use to perform actions. *)

  type lit = Lit.t

  (** {3 Congruence Closure} *)

  (** Congruence closure instance *)
  module CC :
    CC_S
      with module T = T
       and module Lit = Lit
       and type proof = proof
       and type proof_step = proof_step
       and type P.t = proof
       and type P.lit = lit
       and type Actions.t = theory_actions

  val cc : t -> CC.t
  (** Congruence closure for this solver *)

  (** {3 Simplifiers} *)

  (** Simplify terms *)
  module Simplify : sig
    type t

    val tst : t -> term_store
    val ty_st : t -> ty_store

    val clear : t -> unit
    (** Reset internal cache, etc. *)

    val proof : t -> proof
    (** Access proof *)

    type hook = t -> term -> (term * proof_step Iter.t) option
    (** Given a term, try to simplify it. Return [None] if it didn't change.

        A simple example could be a hook that takes a term [t],
        and if [t] is [app "+" (const x) (const y)] where [x] and [y] are number,
        returns [Some (const (x+y))], and [None] otherwise.

        The simplifier will take care of simplifying the resulting term further,
        caching (so that work is not duplicated in subterms), etc.
    *)

    val normalize : t -> term -> (term * proof_step) option
    (** Normalize a term using all the hooks. This performs
        a fixpoint, i.e. it only stops when no hook applies anywhere inside
        the term. *)

    val normalize_t : t -> term -> term * proof_step option
    (** Normalize a term using all the hooks, along with a proof that the
        simplification is correct.
        returns [t, ø] if no simplification occurred. *)
  end

  type simplify_hook = Simplify.hook

  val add_simplifier : t -> Simplify.hook -> unit
  (** Add a simplifier hook for preprocessing. *)

  val simplify_t : t -> term -> (term * proof_step) option
  (** Simplify input term, returns [Some u] if some
      simplification occurred. *)

  val simp_t : t -> term -> term * proof_step option
  (** [simp_t si t] returns [u] even if no simplification occurred
      (in which case [t == u] syntactically).
      It emits [|- t=u].
      (see {!simplifier}) *)

  (** {3 Preprocessors}
      These preprocessors turn mixed, raw literals (possibly simplified) into
      literals suitable for reasoning.
      Typically some clauses are also added to the solver. *)

  module type PREPROCESS_ACTS = sig
    val proof : proof

    val mk_lit : ?sign:bool -> term -> lit
    (** [mk_lit t] creates a new literal for a boolean term [t]. *)

    val add_clause : lit list -> proof_step -> unit
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

  val raise_conflict : t -> theory_actions -> lit list -> proof_step -> 'a
  (** Give a conflict clause to the solver *)

  val push_decision : t -> theory_actions -> lit -> unit
  (** Ask the SAT solver to decide the given literal in an extension of the
      current trail. This is useful for theory combination.
      If the SAT solver backtracks, this (potential) decision is removed
      and forgotten. *)

  val propagate :
    t -> theory_actions -> lit -> reason:(unit -> lit list * proof_step) -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val propagate_l : t -> theory_actions -> lit -> lit list -> proof_step -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val add_clause_temp : t -> theory_actions -> lit list -> proof_step -> unit
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  val add_clause_permanent :
    t -> theory_actions -> lit list -> proof_step -> unit
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

  val cc_raise_conflict_expl : t -> theory_actions -> CC.Expl.t -> 'a
  (** Raise a conflict with the given congruence closure explanation.
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val cc_find : t -> CC.N.t -> CC.N.t
  (** Find representative of the node *)

  val cc_are_equal : t -> term -> term -> bool
  (** Are these two terms equal in the congruence closure? *)

  val cc_merge : t -> theory_actions -> CC.N.t -> CC.N.t -> CC.Expl.t -> unit
  (** Merge these two nodes in the congruence closure, given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val cc_merge_t : t -> theory_actions -> term -> term -> CC.Expl.t -> unit
  (** Merge these two terms in the congruence closure, given this explanation.
      See {!cc_merge} *)

  val cc_add_term : t -> term -> CC.N.t
  (** Add/retrieve congruence closure node for this term.
      To be used in theories *)

  val cc_mem_term : t -> term -> bool
  (** Return [true] if the term is explicitly in the congruence closure.
      To be used in theories *)

  val on_cc_pre_merge :
    t ->
    (CC.t -> theory_actions -> CC.N.t -> CC.N.t -> CC.Expl.t -> unit) ->
    unit
  (** Callback for when two classes containing data for this key are merged (called before) *)

  val on_cc_post_merge :
    t -> (CC.t -> theory_actions -> CC.N.t -> CC.N.t -> unit) -> unit
  (** Callback for when two classes containing data for this key are merged (called after)*)

  val on_cc_new_term : t -> (CC.t -> CC.N.t -> term -> unit) -> unit
  (** Callback to add data on terms when they are added to the congruence
      closure *)

  val on_cc_is_subterm : t -> (CC.N.t -> term -> unit) -> unit
  (** Callback for when a term is a subterm of another term in the
      congruence closure *)

  val on_cc_conflict : t -> (CC.t -> th:bool -> lit list -> unit) -> unit
  (** Callback called on every CC conflict *)

  val on_cc_propagate :
    t -> (CC.t -> lit -> (unit -> lit list * proof_step) -> unit) -> unit
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
    recurse:(t -> CC.N.t -> term) -> t -> CC.N.t -> term option
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

  type proof
  type proof_step

  module P :
    PROOF
      with type lit = Lit.t
       and type t = proof
       and type proof_step = proof_step
       and type term = T.Term.t

  (** Internal solver, available to theories.  *)
  module Solver_internal :
    SOLVER_INTERNAL
      with module T = T
       and module Lit = Lit
       and type proof = proof
       and type proof_step = proof_step
       and module P = P

  type t
  (** The solver's state. *)

  type solver = t
  type term = T.Term.t
  type ty = T.Ty.t
  type lit = Lit.t

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
  val proof : t -> proof

  val create :
    ?stat:Stat.t ->
    ?size:[ `Big | `Tiny | `Small ] ->
    (* TODO? ?config:Config.t -> *)
    proof:proof ->
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

  val add_clause : t -> lit IArray.t -> proof_step -> unit
  (** [add_clause solver cs] adds a boolean clause to the solver.
      Subsequent calls to {!solve} will need to satisfy this clause. *)

  val add_clause_l : t -> lit list -> proof_step -> unit
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
        unsat_proof_step: unit -> proof_step option;
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

(** Helper for the congruence closure

    This helps theories keeping track of some state for each class.
    The state of a class is the monoidal combination of the state for each
    term in the class (for example, the set of terms in the
    class whose head symbol is a datatype constructor). *)
module type MONOID_ARG = sig
  module SI : SOLVER_INTERNAL

  type t
  (** Some type with a monoid structure *)

  val pp : t Fmt.printer

  val name : string
  (** name of the monoid structure (short) *)

  val of_term :
    SI.CC.t -> SI.CC.N.t -> SI.T.Term.t -> t option * (SI.CC.N.t * t) list
  (** [of_term n t], where [t] is the term annotating node [n],
      must return [maybe_m, l], where:
      - [maybe_m = Some m] if [t] has monoid value [m];
        otherwise [maybe_m=None]
      - [l] is a list of [(u, m_u)] where each [u]'s term
        is a direct subterm of [t]
        and [m_u] is the monoid value attached to [u].
      *)

  val merge :
    SI.CC.t ->
    SI.CC.N.t ->
    t ->
    SI.CC.N.t ->
    t ->
    SI.CC.Expl.t ->
    (t, SI.CC.Expl.t) result
  (** Monoidal combination of two values.

      [merge cc n1 mon1 n2 mon2 expl] returns the result of merging
      monoid values [mon1] (for class [n1]) and [mon2] (for class [n2])
      when [n1] and [n2] are merged with explanation [expl].

      @return [Ok mon] if the merge is acceptable, annotating the class of [n1 ∪ n2];
      or [Error expl'] if the merge is unsatisfiable. [expl'] can then be
      used to trigger a conflict and undo the merge.
    *)
end

(** State for a per-equivalence-class monoid.

    Helps keep track of monoid state per equivalence class.
    A theory might use one or more instance(s) of this to
    aggregate some theory-specific state over all terms, with
    the information of what terms are already known to be equal
    potentially saving work for the theory. *)
module Monoid_of_repr (M : MONOID_ARG) : sig
  type t

  val create_and_setup : ?size:int -> M.SI.t -> t
  (** Create a new monoid state *)

  val push_level : t -> unit
  (** Push backtracking point *)

  val pop_levels : t -> int -> unit
  (** Pop [n] backtracking points *)

  val n_levels : t -> int

  val mem : t -> M.SI.CC.N.t -> bool
  (** Does the CC node have a monoid value? *)

  val get : t -> M.SI.CC.N.t -> M.t option
  (** Get monoid value for this CC node, if any *)

  val iter_all : t -> (M.SI.CC.repr * M.t) Iter.t
  val pp : t Fmt.printer
end = struct
  module SI = M.SI
  module T = SI.T.Term
  module N = SI.CC.N
  module CC = SI.CC
  module N_tbl = Backtrackable_tbl.Make (N)
  module Expl = SI.CC.Expl

  type t = {
    cc: CC.t;
    values: M.t N_tbl.t; (* repr -> value for the class *)
    field_has_value: N.bitfield;
        (* bit in CC to filter out quickly classes without value *)
  }

  let push_level self = N_tbl.push_level self.values
  let pop_levels self n = N_tbl.pop_levels self.values n
  let n_levels self = N_tbl.n_levels self.values

  let mem self n =
    let res = CC.get_bitfield self.cc self.field_has_value n in
    assert (
      if res then
        N_tbl.mem self.values n
      else
        true);
    res

  let get self n =
    if CC.get_bitfield self.cc self.field_has_value n then
      N_tbl.get self.values n
    else
      None

  let on_new_term self cc n (t : T.t) : unit =
    (*Log.debugf 50 (fun k->k "(@[monoid[%s].on-new-term.try@ %a@])" M.name N.pp n);*)
    let maybe_m, l = M.of_term cc n t in
    (match maybe_m with
    | Some v ->
      Log.debugf 20 (fun k ->
          k "(@[monoid[%s].on-new-term@ :n %a@ :value %a@])" M.name N.pp n M.pp
            v);
      SI.CC.set_bitfield cc self.field_has_value true n;
      N_tbl.add self.values n v
    | None -> ());
    List.iter
      (fun (n_u, m_u) ->
        Log.debugf 20 (fun k ->
            k "(@[monoid[%s].on-new-term.sub@ :n %a@ :sub-t %a@ :value %a@])"
              M.name N.pp n N.pp n_u M.pp m_u);
        let n_u = CC.find cc n_u in
        if CC.get_bitfield self.cc self.field_has_value n_u then (
          let m_u' =
            try N_tbl.find self.values n_u
            with Not_found ->
              Error.errorf "node %a has bitfield but no value" N.pp n_u
          in
          match M.merge cc n_u m_u n_u m_u' (Expl.mk_list []) with
          | Error expl ->
            Error.errorf
              "when merging@ @[for node %a@],@ values %a and %a:@ conflict %a"
              N.pp n_u M.pp m_u M.pp m_u' CC.Expl.pp expl
          | Ok m_u_merged ->
            Log.debugf 20 (fun k ->
                k
                  "(@[monoid[%s].on-new-term.sub.merged@ :n %a@ :sub-t %a@ \
                   :value %a@])"
                  M.name N.pp n N.pp n_u M.pp m_u_merged);
            N_tbl.add self.values n_u m_u_merged
        ) else (
          (* just add to [n_u] *)
          SI.CC.set_bitfield cc self.field_has_value true n_u;
          N_tbl.add self.values n_u m_u
        ))
      l;
    ()

  let iter_all (self : t) : _ Iter.t = N_tbl.to_iter self.values

  let on_pre_merge (self : t) cc acts n1 n2 e_n1_n2 : unit =
    match get self n1, get self n2 with
    | Some v1, Some v2 ->
      Log.debugf 5 (fun k ->
          k
            "(@[monoid[%s].on_pre_merge@ (@[:n1 %a@ :val1 %a@])@ (@[:n2 %a@ \
             :val2 %a@])@])"
            M.name N.pp n1 M.pp v1 N.pp n2 M.pp v2);
      (match M.merge cc n1 v1 n2 v2 e_n1_n2 with
      | Ok v' ->
        N_tbl.remove self.values n2;
        (* only keep repr *)
        N_tbl.add self.values n1 v'
      | Error expl -> SI.CC.raise_conflict_from_expl cc acts expl)
    | None, Some cr ->
      SI.CC.set_bitfield cc self.field_has_value true n1;
      N_tbl.add self.values n1 cr;
      N_tbl.remove self.values n2 (* only keep reprs *)
    | Some _, None -> () (* already there on the left *)
    | None, None -> ()

  let pp out (self : t) : unit =
    let pp_e out (t, v) = Fmt.fprintf out "(@[%a@ :has %a@])" N.pp t M.pp v in
    Fmt.fprintf out "(@[%a@])" (Fmt.iter pp_e) (iter_all self)

  let create_and_setup ?size (solver : SI.t) : t =
    let cc = SI.cc solver in
    let field_has_value =
      SI.CC.allocate_bitfield ~descr:("monoid." ^ M.name ^ ".has-value") cc
    in
    let self = { cc; values = N_tbl.create ?size (); field_has_value } in
    SI.on_cc_new_term solver (on_new_term self);
    SI.on_cc_pre_merge solver (on_pre_merge self);
    self
end
