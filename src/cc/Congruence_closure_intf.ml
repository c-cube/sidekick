
module type ARG = CC_types.FULL

module type THEORY_KEY = sig
  type ('term,'lit,'a) t
  (** An access key for theories which have per-class data ['a] *)

  val create :
    ?pp:'a Fmt.printer ->
    name:string ->
    eq:('a -> 'a -> bool) ->
    merge:('a -> 'a -> 'a) ->
    unit ->
    ('term,'lit,'a) t
  (** Generative creation of keys for the given theory data.

      @param eq : Equality. This is used to optimize backtracking info.

      @param merge :
        [merge d1 d2] is called when merging classes with data [d1] and [d2]
        respectively. The theory should already have checked that the merge
        is compatible, and this produces the combined data  for terms in the
        merged class.
      @param name name of the theory which owns this data
      @param pp a printer for the data
  *)

  val equal : ('t,'lit,_) t -> ('t,'lit,_) t -> bool
  (** Checks if two keys are equal (generatively) *)

  val pp : _ t Fmt.printer
  (** Prints the name of the key. *)
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

    val iter_class : t -> t Iter.t
    (** Traverse the congruence class.
        Invariant: [is_root n] (see {!find} below) *)

    val iter_parents : t -> t Iter.t
    (** Traverse the parents of the class.
        Invariant: [is_root n] (see {!find} below) *)
  end

  module Expl : sig
    type t
    val pp : t Fmt.printer

    val mk_merge : N.t -> N.t -> t
    val mk_lit : lit -> t
    val mk_list : t list -> t
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

  module Theory : sig
    type cc = t
    type t

    type 'a key = (term,lit,'a) Key.t

    val raise_conflict : cc -> Expl.t -> unit
    (** Raise a conflict with the given explanation
        it must be a theory tautology that [expl ==> absurd].
        To be used in theories. *)

    val merge : cc -> N.t -> N.t -> Expl.t -> unit
    (** Merge these two nodes given this explanation.
        It must be a theory tautology that [expl ==> n1 = n2].
        To be used in theories. *)

    val add_term : cc -> term -> N.t
    (** Add/retrieve node for this term.
        To be used in theories *)

    val get_data : cc -> N.t -> 'a key -> 'a option
    (** Get data information for this particular representative *)

    val add_data : cc -> N.t -> 'a key -> 'a -> unit
    (** Add data to this particular representative. Will be backtracked. *)

    val make :
      key:'a key ->
      on_merge:(cc -> N.t -> 'a -> N.t -> 'a -> Expl.t -> unit) ->
      on_new_term:(cc -> N.t -> term -> 'a option) ->
      unit ->
      t
    (** Build a micro theory. It can use the callbacks above. *)
  end

  val create :
    ?stat:Stat.t ->
    ?th:Theory.t list ->
    ?on_merge:(t -> N.t -> N.t -> Expl.t -> unit) list ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure. *)

  val add_th : t -> Theory.t -> unit
  (** Add a (micro) theory to the congruence closure.
      @raise Error.Error if there is already a theory with
      the same key. *)

  val on_merge : t -> (t -> N.t -> N.t -> Expl.t -> unit) -> unit
  (** Add a function to be called when two classes are merged *)

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

  val assert_eq : t -> term -> term -> lit list -> unit
  (** merge the given terms with some explanations *)

  (* TODO: remove and move into its own library as a micro theory
  val assert_distinct : t -> term list -> neq:term -> lit -> unit
  (** [assert_distinct l ~neq:u e] asserts all elements of [l] are distinct
      because [lit] is true
      precond: [u = distinct l] *)
     *)

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
