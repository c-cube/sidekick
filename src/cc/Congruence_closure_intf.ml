
module type ARG = CC_types.FULL

(** Data stored by a theory for its own terms.

    It needs to form a commutative monoid where values can be unmerged upon
    backtracking.
*)
module type THEORY_DATA = sig
  type term
  type t

  val empty : t

  val equal : t -> t -> bool
  (** Equality. This is used to optimize backtracking info. *)

  val merge : t -> t -> t
  (** [merge d1 d2] is called when merging classes with data [d1] and [d2]
      respectively. The theory should already have checked that the merge
      is compatible, and this produces the combined data  for terms in the
      merged class. *)
end

type ('t, 'a) theory_data = (module THEORY_DATA with type term = 't and type t = 'a)

module type THEORY_KEY = sig
  type ('t, 'a) t
  (** An access key for theories that use terms ['t] and which have
      per-class data ['a] *)

  val create : ('t, 'a) theory_data -> ('t, 'a) t
  (** Generative creation of keys for the given theory data. *)
end

module type S = sig
  type term_state
  type term
  type fun_
  type lit
  type proof
  type model

  (** Implementation of theory keys *)
  module Key : THEORY_KEY

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
    (** Is the node a root (ie the representative of its class)? *)

    val iter_class : t -> t Sequence.t
    (** Traverse the congruence class.
        Invariant: [is_root n] (see {!find} below) *)

    val iter_parents : t -> t Sequence.t
    (** Traverse the parents of the class.
        Invariant: [is_root n] (see {!find} below) *)
  end

  module Expl : sig
    type t
    val pp : t Fmt.printer

    val mk_reduction : t
    val mk_congruence : N.t -> N.t -> t
    val mk_merge : N.t -> N.t -> t
    val mk_merges : (N.t * N.t) list -> t
    val mk_lit : lit -> t
    val mk_lits : lit list -> t
  end

  type node = N.t
  (** A node of the congruence closure *)

  type repr = N.t
  (** Node that is currently a representative *)

  type explanation = Expl.t

  type conflict = lit list

  (** Accessors *)

  val term_state : t -> term_state

  val find : t -> node -> repr
  (** Current representative *)

  val add_term : t -> term -> node
  (** Add the term to the congruence closure, if not present already.
      Will be backtracked. *)

  (** Actions available to the theory *)
  type sat_actions = (Msat.void, lit, Msat.void, proof) Msat.acts

  val create :
    ?on_merge:(t -> repr -> repr -> explanation -> unit) list ->
    ?on_new_term:(t -> repr -> term -> unit) list ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure. *)

  val on_merge : t -> (t -> repr -> repr -> explanation -> unit) -> unit
  (** Add a callback, to be called whenever two classes are merged *)

  val on_new_term : t -> (t -> repr -> term -> unit) -> unit
  (** Add a callback, to be called whenever a node is added *)

  val merge_classes : t -> node -> node -> explanation -> unit
  (** Merge the two given nodes with given explanation.
      It must be a theory tautology that [expl ==> n1 = n2] *)

  val th_data_get : t -> N.t -> (term, 'a) Key.t -> 'a option
  (** Get data information for this particular representative *)

  val th_data_add : t -> N.t -> (term, 'a) Key.t -> 'a -> unit
  (** Add the given data to this node (or rather, to its representative).
      This will be backtracked. *)

  (* TODO: merge true/false? 
  val raise_conflict : CC.t -> CC.N.t -> CC.N.t -> Expl.t -> 'a
     *)

  val set_as_lit : t -> N.t -> lit -> unit
  (** map the given node to a literal. *)

  val find_t : t -> term -> repr
  (** Current representative of the term.
      @raise Not_found if the term is not already {!add}-ed. *)

  val add_seq : t -> term Sequence.t -> unit
  (** Add a sequence of terms to the congruence closure *)

  val all_classes : t -> repr Sequence.t
  (** All current classes. This is costly, only use if there is no other solution *)

  val assert_lit : t -> lit -> unit
  (** Given a literal, assume it in the congruence closure and propagate
      its consequences. Will be backtracked.
  
      Useful for the theory combination or the SAT solver's functor *)

  val assert_lits : t -> lit Sequence.t -> unit
  (** Addition of many literals *)

  val assert_eq : t -> term -> term -> lit list -> unit
  (** merge the given terms with some explanations *)

  (* TODO: remove and move into its own library as a micro theory *)
  val assert_distinct : t -> term list -> neq:term -> lit -> unit
  (** [assert_distinct l ~neq:u e] asserts all elements of [l] are distinct
      because [lit] is true
      precond: [u = distinct l] *)

  val check : t -> sat_actions -> unit
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the [sat_actions] to propagate literals, declare conflicts, etc. *)

  val push_level : t -> unit
  (** Push backtracking level *)

  val pop_levels : t -> int -> unit
  (** Restore to state [n] calls to [push_level] earlier. Used during backtracking. *)

  val mk_model : t -> model -> model
  (** Enrich a model by mapping terms to their representative's value,
      if any. Otherwise map the representative to a fresh value *)

  (**/**)
  val check_invariants : t -> unit
  val pp_full : t Fmt.printer
  (**/**)

end
