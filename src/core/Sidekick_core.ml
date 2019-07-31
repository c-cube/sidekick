(** {1 Main Environment}

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
*)

module Fmt = CCFormat

module type MERGE_PP = sig
  type t
  val merge : t -> t -> t
  val pp : t Fmt.printer
end

module CC_view = struct
  type ('f, 't, 'ts) t =
    | Bool of bool
    | App_fun of 'f * 'ts
    | App_ho of 't * 'ts
    | If of 't * 't * 't
    | Eq of 't * 't
    | Not of 't
    | Opaque of 't (* do not enter *)

  let map_view ~f_f ~f_t ~f_ts (v:_ t) : _ t =
    match v with
    | Bool b -> Bool b
    | App_fun (f, args) -> App_fun (f_f f, f_ts args)
    | App_ho (f, args) -> App_ho (f_t f, f_ts args)
    | Not t -> Not (f_t t)
    | If (a,b,c) -> If (f_t a, f_t b, f_t c)
    | Eq (a,b) -> Eq (f_t a, f_t b)
    | Opaque t -> Opaque (f_t t)

  let iter_view ~f_f ~f_t ~f_ts (v:_ t) : unit =
    match v with
    | Bool _ -> ()
    | App_fun (f, args) -> f_f f; f_ts args
    | App_ho (f, args) -> f_t f; f_ts args
    | Not t -> f_t t
    | If (a,b,c) -> f_t a; f_t b; f_t c;
    | Eq (a,b) -> f_t a; f_t b
    | Opaque t -> f_t t
end

module type TERM = sig
  module Fun : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  module Ty : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    val bool : t
    val is_bool : t -> bool
  end

  module Term : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    type state

    val ty : t -> Ty.t
    val bool : state -> bool -> t (* build true/false *)
    val as_bool : t -> bool option

    val abs : state -> t -> t * bool

    val map_shallow : state -> (t -> t) -> t -> t
    (** Map function on immediate subterms *)

    val iter_dag : t -> (t -> unit) -> unit

    module Tbl : CCHashtbl.S with type key = t
  end
end

module type TERM_PROOF = sig
  include TERM

  module Proof : sig
    type t
    val pp : t Fmt.printer

    val default : t
  end
end

module type CC_ARG = sig
  module A : TERM_PROOF

  val cc_view : A.Term.t -> (A.Fun.t, A.Term.t, A.Term.t Iter.t) CC_view.t
  (** View the term through the lens of the congruence closure *)

  module Lit : sig
    type t
    val term : t -> A.Term.t
    val sign : t -> bool
    val neg : t -> t
    val pp : t Fmt.printer
  end

  module Actions : sig
    type t

    val raise_conflict : t -> Lit.t list -> A.Proof.t -> 'a

    val propagate : t -> Lit.t -> reason:(unit -> Lit.t list) -> A.Proof.t -> unit
  end
end

module type CC_S = sig
  module A : CC_ARG 
  type term_state = A.A.Term.state
  type term = A.A.Term.t
  type fun_ = A.A.Fun.t
  type lit = A.Lit.t
  type proof = A.A.Proof.t
  type actions = A.Actions.t

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
        Precondition: [is_root n] (see {!find} below) *)

    val iter_parents : t -> t Iter.t
    (** Traverse the parents of the class.
        Precondition: [is_root n] (see {!find} below) *)

    type bitfield
    (** A field in the bitfield of this node. This should only be
        allocated when a theory is initialized.

        All fields are initially 0, are backtracked automatically,
        and are merged automatically when classes are merged. *)

    val get_field : bitfield -> t -> bool
    val set_field : bitfield -> bool -> t -> unit
  end

  module Expl : sig
    type t
    val pp : t Fmt.printer

    val mk_merge : N.t -> N.t -> t
    val mk_merge_t : term -> term -> t
    val mk_lit : lit -> t
    val mk_list : t list -> t
  end

  type node = N.t
  (** A node of the congruence closure *)

  type repr = N.t
  (** Node that is currently a representative *)

  type explanation = Expl.t

  (** Accessors *)

  val term_state : t -> term_state

  val find : t -> node -> repr
  (** Current representative *)

  val add_term : t -> term -> node
  (** Add the term to the congruence closure, if not present already.
      Will be backtracked. *)

  type ev_on_merge = t -> actions -> N.t -> N.t -> Expl.t -> unit
  type ev_on_new_term = t -> N.t -> term -> unit
  type ev_on_conflict = t -> lit list -> unit
  type ev_on_propagate = t -> lit -> (unit -> lit list) -> unit

  val create :
    ?stat:Stat.t ->
    ?on_merge:ev_on_merge list ->
    ?on_new_term:ev_on_new_term list ->
    ?on_conflict:ev_on_conflict list ->
    ?on_propagate:ev_on_propagate list ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure. *)

  val allocate_bitfield : t -> N.bitfield
  (** Allocate a new bitfield for the nodes.
      See {!N.bitfield}. *)

  (* TODO: remove? this is managed by the solver anyway? *)
  val on_merge : t -> ev_on_merge -> unit
  (** Add a function to be called when two classes are merged *)

  val on_new_term : t -> ev_on_new_term -> unit
  (** Add a function to be called when a new node is created *)

  val on_conflict : t -> ev_on_conflict -> unit
  (** Called when the congruence closure finds a conflict *)

  val on_propagate : t -> ev_on_propagate -> unit
  (** Called when the congruence closure propagates a literal *)

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

  val raise_conflict_from_expl : t -> actions -> Expl.t -> 'a
  (** Raise a conflict with the given explanation
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val merge : t -> N.t -> N.t -> Expl.t -> unit
  (** Merge these two nodes given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val merge_t : t -> term -> term -> Expl.t -> unit
  (** Shortcut for adding + merging *)

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

(** A view of the solver from a theory's point of view *)
module type SOLVER_INTERNAL = sig
  module A : TERM_PROOF 
  module CC_A : CC_ARG with module A = A
  module CC : CC_S with module A = CC_A

  type ty = A.Ty.t
  type term = A.Term.t
  type term_state = A.Term.state
  type proof = A.Proof.t

  (** {3 Main type for a solver} *)
  type t
  type solver = t

  val tst : t -> term_state

  val cc : t -> CC.t
  (** Congruence closure for this solver *)

  (** {3 Literals}

      A literal is a (preprocessed) term along with its sign.
      It is directly manipulated by the SAT solver.
  *)
  module Lit : sig
    type t
    val term : t -> term
    val sign : t -> bool
    val neg : t -> t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end
  type lit = Lit.t

  (** {3 Simplifiers} *)

  module Simplify : sig
    type t

    val tst : t -> term_state

    val clear : t -> unit
    (** Reset internal cache, etc. *)

    type hook = t -> term -> term option
    (** Given a term, try to simplify it. Return [None] if it didn't change.
        Can also add clauses to the simplifier. *)

    val normalize : t -> term -> term
    (** Normalize a term using all the hooks. *)
  end

  type simplify_hook = Simplify.hook

  val add_simplifier : t -> Simplify.hook -> unit

  val simplifier : t -> Simplify.t

  val simp_t : t -> term -> term

  (** {3 hooks for the theory} *)

  type actions = CC_A.Actions.t

  val propagate : t -> actions -> lit -> reason:(unit -> lit list) -> A.Proof.t -> unit

  val raise_conflict : t -> actions -> lit list -> A.Proof.t -> 'a
  (** Give a conflict clause to the solver *)

  val propagate: t -> actions -> lit -> (unit -> lit list) -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val propagate_l: t -> actions -> lit -> lit list -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val add_clause_temp : t -> actions -> lit list -> unit
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  val add_clause_permanent : t -> actions -> lit list -> unit
  (** Add toplevel clause to the SAT solver. This clause will
      not be backtracked. *)

  val mk_lit : t -> actions -> ?sign:bool -> term -> lit
  (** Create a literal *)

  val add_lit : t -> actions -> lit -> unit
  (** Add the given literal to the SAT solver, so it gets assigned
      a boolean value *)

  val add_lit_t : t -> actions -> ?sign:bool -> term -> unit
  (** Add the given (signed) bool term to the SAT solver, so it gets assigned
      a boolean value *)

  val cc_raise_conflict_expl : t -> actions -> CC.Expl.t -> 'a
  (** Raise a conflict with the given congruence closure explanation.
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val cc_find : t -> CC.N.t -> CC.N.t
  (** Find representative of the node *)

  val cc_merge : t -> actions -> CC.N.t -> CC.N.t -> CC.Expl.t -> unit
  (** Merge these two nodes in the congruence closure, given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val cc_merge_t : t -> actions -> term -> term -> CC.Expl.t -> unit
  (** Merge these two terms in the congruence closure, given this explanation.
      See {!cc_merge} *)

  val cc_add_term : t -> term -> CC.N.t
  (** Add/retrieve congruence closure node for this term.
      To be used in theories *)

  val on_cc_merge : t -> (CC.t -> actions -> CC.N.t -> CC.N.t -> CC.Expl.t -> unit) -> unit
  (** Callback for when two classes containing data for this key are merged *)

  val on_cc_new_term : t -> (CC.t -> CC.N.t -> term -> unit) -> unit
  (** Callback to add data on terms when they are added to the congruence
      closure *)

  val on_cc_conflict : t -> (CC.t -> lit list -> unit) -> unit
  (** Callback called on every CC conflict *)

  val on_cc_propagate : t -> (CC.t -> lit -> (unit -> lit list) -> unit) -> unit
  (** Callback called on every CC propagation *)

  val on_partial_check : t -> (t -> actions -> lit Iter.t -> unit) -> unit
  (** Register callbacked to be called with the slice of literals
      newly added on the trail.

      This is called very often and should be efficient. It doesn't have
      to be complete, only correct. It's given only the slice of
      the trail consisting in new literals. *)

  val on_final_check: t -> (t -> actions -> lit Iter.t -> unit) -> unit
  (** Register callback to be called during the final check.

      Must be complete (i.e. must raise a conflict if the set of literals is
      not satisfiable) and can be expensive. The function
      is given the whole trail. *)

  (** {3 Preprocessors}
      These preprocessors turn mixed, raw literals (possibly simplified) into
      literals suitable for reasoning.
      Typically some clauses are also added to the solver. *)

  type preprocess_hook =
    t ->
    mk_lit:(term -> lit) ->
    add_clause:(lit list -> unit) ->
    term -> term option
  (** Given a term, try to preprocess it. Return [None] if it didn't change.
      Can also add clauses to define new terms. *)

  val add_preprocess : t -> preprocess_hook -> unit
end

(** Public view of the solver *)
module type SOLVER = sig
  module A : TERM_PROOF
  module CC_A : CC_ARG with module A = A
  module Solver_internal : SOLVER_INTERNAL with module A = A and module CC_A = CC_A
  (** Internal solver, available to theories.  *)

  type t
  type solver = t
  type term = A.Term.t
  type ty = A.Ty.t
  type lit = Solver_internal.Lit.t
  type lemma = A.Proof.t

  (** {3 A theory}


      Theories are abstracted over the concrete implementation of the solver,
      so they can work with any implementation.

      Typically a theory should be a functor taking an argument containing
      a [SOLVER_INTERNAL] and some additional views on terms, literals, etc.
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
    (** Name of the theory *)

    val create_and_setup : Solver_internal.t -> t
    (** Instantiate the theory's state for the given (internal) solver,
        register callbacks, create keys, etc. *)

    val push_level : t -> unit
    (** Push backtracking level *)

    val pop_levels : t -> int -> unit
    (** Pop backtracking levels, restoring the theory to its former state *)
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
  (** Helper to create a theory *)

  (** {3 Boolean Atoms} *)
  module Atom : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t CCFormat.printer

    val formula : t -> lit
    val sign : t -> bool
  end

  (** {3 Semantic values} *)
  module Value : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val ty : t -> ty
    val pp : t Fmt.printer
  end

  module Model : sig
    type t

    val empty : t

    val mem : term -> t -> bool

    val find : term -> t -> Value.t option

    val eval : t -> term -> Value.t option

    val pp : t Fmt.printer
  end

  module Unknown : sig
    type t
    val pp : t CCFormat.printer

    (*
    type unknown =
      | U_timeout
      | U_incomplete
       *)
  end

  module Proof : sig
    type t
    val check : t -> unit
    val pp_dot : t Fmt.printer
  end
  type proof = Proof.t

  (** {3 Main API} *)

  val stats : t -> Stat.t
  val tst : t -> A.Term.state

  val create :
    ?stat:Stat.t ->
    ?size:[`Big | `Tiny | `Small] ->
    (* TODO? ?config:Config.t -> *)
    ?store_proof:bool ->
    theories:theory list ->
    A.Term.state ->
    unit ->
    t
  (** Create a new solver.
      @param theories theories to load from the start. *)

  val add_theory : t -> theory -> unit
  (** Add a theory to the solver. This should be called before
      any call to {!solve} or to {!add_clause} and the likes (otherwise
      the theory will have a partial view of the problem). *)

  val add_theory_p : t -> 'a theory_p -> 'a
  (** Add the given theory and obtain its state *)

  val add_theory_l : t -> theory list -> unit

  val mk_atom_lit : t -> lit -> Atom.t

  val mk_atom_t : t -> ?sign:bool -> term -> Atom.t

  val add_clause : t -> Atom.t IArray.t -> unit

  val add_clause_l : t -> Atom.t list -> unit

  type res =
    | Sat of Model.t
    | Unsat of {
        proof: proof option;
        unsat_core: Atom.t list lazy_t;
      }
    | Unknown of Unknown.t
    (** Result of solving for the current set of clauses *)

  val solve :
    ?on_exit:(unit -> unit) list ->
    ?check:bool ->
    ?on_progress:(t -> unit) ->
    assumptions:Atom.t list ->
    t ->
    res
  (** [solve s] checks the satisfiability of the statement added so far to [s]
      @param check if true, the model is checked before returning
      @param assumptions a set of atoms held to be true. The unsat core,
        if any, will be a subset of [assumptions].
      @param on_exit functions to be run before this returns *)

  val pp_term_graph: t CCFormat.printer
  val pp_stats : t CCFormat.printer
end
