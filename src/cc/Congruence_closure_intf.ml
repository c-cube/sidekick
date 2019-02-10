
module type ARG = CC_types.FULL

(** Theory-extensible payloads in the equivalence classes *)
type payload = ..

module type S = sig
  type term_state
  type term
  type fun_
  type lit
  type proof
  type model

  (** Actions available to the theory *)
  type sat_actions = (Msat.void, lit, Msat.void, proof) Msat.acts

  type t
  (** Global state of the congruence closure *)


  (** An equivalence class is a set of terms that are currently equal
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

    val term : t -> term
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    val is_root : t -> bool

    val iter_class : t -> t Sequence.t
    (** Traverse the congruence class.
        Invariant: [is_root n] (see {!find} below) *)

    val iter_parents : t -> t Sequence.t
    (** Traverse the parents of the class.
        Invariant: [is_root n] (see {!find} below) *)

    type nonrec payload = payload = ..

    val payload_find: f:(payload -> 'a option) -> t -> 'a option

    val payload_pred: f:(payload -> bool) -> t -> bool

    val set_payload : ?can_erase:(payload -> bool) -> t -> payload -> unit
    (** Add given payload
        @param can_erase if provided, checks whether an existing value
        is to be replaced instead of adding a new entry *)
  end

  module Expl : sig
    type t
    val pp : t Fmt.printer
  end

  type node = N.t
  (** A node of the congruence closure *)

  type repr = N.t
  (** Node that is currently a representative *)

  type explanation = Expl.t

  type conflict = lit list

  (* TODO micro theories as parameters *)
  val create :
    ?on_merge:(repr -> repr -> explanation -> unit) ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure.
      @param on_merge callback to be called on every merge
  *)

  val find : t -> node -> repr
  (** Current representative *)

  val add_term : t -> term -> node
  (** Add the term to the congruence closure, if not present already.
      Will be backtracked. *)

  val set_as_lit : t -> N.t -> lit -> unit
  (** map the given node to a literal. *)

  val add_term' : t -> term -> unit
  (** Same as {!add_term} but ignore the result *)

  val find_t : t -> term -> repr
  (** Current representative of the term.
      @raise Not_found if the term is not already {!add}-ed. *)

  val add_seq : t -> term Sequence.t -> unit
  (** Add a sequence of terms to the congruence closure *)

  val all_classes : t -> repr Sequence.t
  (** All current classes *)

  val assert_lit : t -> lit -> unit
  (** Given a literal, assume it in the congruence closure and propagate
      its consequences. Will be backtracked. *)

  val assert_lits : t -> lit Sequence.t -> unit

  val assert_eq : t -> term -> term -> lit list -> unit
  (** merge the given terms with some explanations *)

  val assert_distinct : t -> term list -> neq:term -> lit -> unit
  (** [assert_distinct l ~neq:u e] asserts all elements of [l] are distinct
      because [lit] is true
      precond: [u = distinct l] *)

  val check : t -> sat_actions -> unit
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the [sat_actions] to propagate literals, declare conflicts, etc. *)

  val push_level : t -> unit

  val pop_levels : t -> int -> unit

  val mk_model : t -> model -> model
  (** Enrich a model by mapping terms to their representative's value,
      if any. Otherwise map the representative to a fresh value *)

  (**/**)
  val check_invariants : t -> unit
  val pp_full : t Fmt.printer
  (**/**)
end
