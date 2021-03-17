(** {1 Main Environment}

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
*)

module Fmt = CCFormat

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

    type state

    val bool : state -> t
    val is_bool : t -> bool
  end

  module Term : sig
    type t
    val equal : t -> t -> bool
    val compare : t -> t -> int
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

module type PROOF = sig
  type t
  val pp : t Fmt.printer

  val default : t
end

module type LIT = sig
  module T : TERM
  type t

  val term : t -> T.Term.t
  val sign : t -> bool
  val neg : t -> t
  val abs : t -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer
end

module type CC_ACTIONS = sig
  module T : TERM
  module P : PROOF
  module Lit : LIT with module T = T
  type t

  val raise_conflict : t -> Lit.t list -> P.t -> 'a

  val propagate : t -> Lit.t -> reason:(unit -> Lit.t list) -> P.t -> unit
end

module type CC_ARG = sig
  module T : TERM
  module P : PROOF
  module Lit : LIT with module T = T
  module Actions : CC_ACTIONS with module T=T and module P = P and module Lit = Lit

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t
  (** View the term through the lens of the congruence closure *)
end

module type CC_S = sig
  module T : TERM
  module P : PROOF
  module Lit : LIT with module T = T
  module Actions : CC_ACTIONS with module T = T and module Lit = Lit and module P = P
  type term_state = T.Term.state
  type term = T.Term.t
  type fun_ = T.Fun.t
  type lit = Lit.t
  type proof = P.t
  type actions = Actions.t

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
  end

  module Expl : sig
    type t
    val pp : t Fmt.printer

    val mk_merge : N.t -> N.t -> t
    val mk_merge_t : term -> term -> t
    val mk_lit : lit -> t
    val mk_list : t list -> t
    val mk_theory : t -> t (* TODO: indicate what theory, or even provide a lemma *)
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

  val mem_term : t -> term -> bool
  (** Returns [true] if the term is explicitly present in the congruence closure *)

  type ev_on_pre_merge = t -> actions -> N.t -> N.t -> Expl.t -> unit
  type ev_on_post_merge = t -> actions -> N.t -> N.t -> unit
  type ev_on_new_term = t -> N.t -> term -> unit
  type ev_on_conflict = t -> th:bool -> lit list -> unit
  type ev_on_propagate = t -> lit -> (unit -> lit list) -> unit
  type ev_on_is_subterm = N.t -> term -> unit

  val create :
    ?stat:Stat.t ->
    ?on_pre_merge:ev_on_pre_merge list ->
    ?on_post_merge:ev_on_post_merge list ->
    ?on_new_term:ev_on_new_term list ->
    ?on_conflict:ev_on_conflict list ->
    ?on_propagate:ev_on_propagate list ->
    ?on_is_subterm:ev_on_is_subterm list ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure. *)

  val allocate_bitfield : descr:string -> t -> N.bitfield
  (** Allocate a new bitfield for the nodes.
      See {!N.bitfield}. *)

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

  val explain_eq : t -> N.t -> N.t -> lit list
  (** Explain why the two nodes are equal.
      Fails if they are not, in an unspecified way *)

  val raise_conflict_from_expl : t -> actions -> Expl.t -> 'a
  (** Raise a conflict with the given explanation
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val n_true : t -> N.t
  val n_false : t -> N.t
  val n_bool : t -> bool -> N.t

  val merge : t -> N.t -> N.t -> Expl.t -> unit
  (** Merge these two nodes given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val merge_t : t -> term -> term -> Expl.t -> unit
  (** Shortcut for adding + merging *)

  val check : t -> actions -> unit
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the {!actions} to propagate literals, declare conflicts, etc. *)

  val new_merges : t -> bool
  (** Called after {!check}, returns [true] if some pairs of classes
      were merged. *)

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
  module T : TERM
  module P : PROOF

  type ty = T.Ty.t
  type term = T.Term.t
  type term_state = T.Term.state
  type ty_state = T.Ty.state
  type proof = P.t

  (** {3 Main type for a solver} *)
  type t
  type solver = t

  val tst : t -> term_state
  val ty_st : t -> ty_state
  val stats : t -> Stat.t

  (** {3 Actions for the theories} *)

  type actions

  (** {3 Literals}

      A literal is a (preprocessed) term along with its sign.
      It is directly manipulated by the SAT solver.
  *)
  module Lit : LIT with module T = T

  type lit = Lit.t

  (** {2 Congruence Closure} *)

  module CC : CC_S
    with module T = T
     and module P = P
     and module Lit = Lit
     and type Actions.t = actions

  val cc : t -> CC.t
  (** Congruence closure for this solver *)

  (** {3 Simplifiers} *)

  module Simplify : sig
    type t

    val tst : t -> term_state
    val ty_st : t -> ty_state

    val clear : t -> unit
    (** Reset internal cache, etc. *)

    type hook = t -> term -> term option
    (** Given a term, try to simplify it. Return [None] if it didn't change. *)

    val normalize : t -> term -> term
    (** Normalize a term using all the hooks. *)
  end

  type simplify_hook = Simplify.hook

  val add_simplifier : t -> Simplify.hook -> unit

  val simplifier : t -> Simplify.t

  val simp_t : t -> term -> term

  (** {3 hooks for the theory} *)

  val propagate : t -> actions -> lit -> reason:(unit -> lit list) -> proof -> unit
  (** Propagate a literal for a reason. This is similar to asserting
      the clause [reason => lit], but more lightweight, and in a way
      that is backtrackable. *)

  val raise_conflict : t -> actions -> lit list -> proof -> 'a
  (** Give a conflict clause to the solver *)

  val push_decision : t -> actions -> lit -> unit
  (** Ask the SAT solver to decide the given literal in an extension of the
      current trail. This is useful for theory combination.
      If the SAT solver backtracks, this (potential) decision is removed
      and forgotten. *)

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

  val cc_are_equal : t -> term -> term -> bool
  (** Are these two terms equal in the congruence closure? *)

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

  val cc_mem_term : t -> term -> bool
  (** Return [true] if the term is explicitly in the congruence closure.
      To be used in theories *)

  val on_cc_pre_merge : t -> (CC.t -> actions -> CC.N.t -> CC.N.t -> CC.Expl.t -> unit) -> unit
  (** Callback for when two classes containing data for this key are merged (called before) *)

  val on_cc_post_merge : t -> (CC.t -> actions -> CC.N.t -> CC.N.t -> unit) -> unit
  (** Callback for when two classes containing data for this key are merged (called after)*)

  val on_cc_new_term : t -> (CC.t -> CC.N.t -> term -> unit) -> unit
  (** Callback to add data on terms when they are added to the congruence
      closure *)

  val on_cc_is_subterm : t -> (CC.N.t -> term -> unit) -> unit
  (** Callback for when a term is a subterm of another term in the
      congruence closure *)

  val on_cc_conflict : t -> (CC.t -> th:bool -> lit list -> unit) -> unit
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
      is given the whole trail.
  *)

  (** {3 Preprocessors}
      These preprocessors turn mixed, raw literals (possibly simplified) into
      literals suitable for reasoning.
      Typically some clauses are also added to the solver. *)

  type preprocess_hook =
    t ->
    recurse:(term -> term) ->
    mk_lit:(term -> lit) ->
    add_clause:(lit list -> unit) ->
    term -> term option
  (** Given a term, try to preprocess it. Return [None] if it didn't change.
      Can also add clauses to define new terms.
      @param recurse call preprocessor on subterms.
      @param mk_lit creates a new literal for a boolean term.
      @param add_clause pushes a new clause into the SAT solver.
  *)

  val add_preprocess : t -> preprocess_hook -> unit
end

(** Public view of the solver *)
module type SOLVER = sig
  module T : TERM
  module P : PROOF
  module Lit : LIT with module T = T
  module Solver_internal
    : SOLVER_INTERNAL
      with module T = T
       and module P = P
       and module Lit = Lit
  (** Internal solver, available to theories.  *)

  type t
  type solver = t
  type term = T.Term.t
  type ty = T.Ty.t
  type lit = Lit.t
  type lemma = P.t

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

    val neg : t -> t
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

    val mem : t -> term -> bool

    val find : t -> term -> Value.t option

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
  val tst : t -> T.Term.state
  val ty_st : t -> T.Ty.state

  val create :
    ?stat:Stat.t ->
    ?size:[`Big | `Tiny | `Small] ->
    (* TODO? ?config:Config.t -> *)
    ?store_proof:bool ->
    theories:theory list ->
    T.Term.state ->
    T.Ty.state ->
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

  val pp_stats : t CCFormat.printer
end

(** Helper for keeping track of state for each class *)

module type MONOID_ARG = sig
  module SI : SOLVER_INTERNAL
  type t
  val pp : t Fmt.printer
  val name : string
  (** name of the monoid's value (short) *)

  val of_term :
    SI.CC.N.t -> SI.T.Term.t ->
    (t option * (SI.T.Term.t * t) list)
  (** [of_term n t], where [t] is the term annotating node [n],
      returns [maybe_m, l], where:
      - [maybe_m = Some m] if [t] has monoid value [m];
        otherwise [maybe_m=None]
      - [l] is a list of [(u, m_u)] where each [u] is a direct subterm of [t]
        and [m_u] is the monoid value attached to [u].
      *)

  val merge :
    SI.CC.t ->
    SI.CC.N.t -> t -> SI.CC.N.t -> t ->
    SI.CC.Expl.t ->
    (t, SI.CC.Expl.t) result
end

(** Keep track of monoid state per equivalence class *)
module Monoid_of_repr(M : MONOID_ARG) : sig
  type t
  val create_and_setup : ?size:int -> M.SI.t -> t
  val push_level : t -> unit
  val pop_levels : t -> int -> unit
  val mem : t -> M.SI.CC.N.t -> bool
  val get : t -> M.SI.CC.N.t -> M.t option
  val iter_all : t -> (M.SI.CC.repr * M.t) Iter.t
  val pp : t Fmt.printer
end = struct
  module SI = M.SI
  module T = SI.T.Term
  module N = SI.CC.N
  module CC = SI.CC
  module N_tbl = Backtrackable_tbl.Make(N)
  module Expl = SI.CC.Expl

  type t = {
    values: M.t N_tbl.t; (* repr -> value for the class *)
    field_has_value: N.bitfield; (* bit in CC to filter out quickly classes without value *)
  }

  let push_level self = N_tbl.push_level self.values
  let pop_levels self n = N_tbl.pop_levels self.values n

  let mem self n =
    let res = N.get_field self.field_has_value n in
    assert (if res then N_tbl.mem self.values n else true);
    res

  let get self n =
    if N.get_field self.field_has_value n
    then N_tbl.get self.values n
    else None

  let on_new_term self cc n (t:T.t) : unit =
    let maybe_m, l = M.of_term n t in
    begin match maybe_m with
      | Some v ->
        Log.debugf 20
          (fun k->k "(@[monoid[%s].on-new-term@ :n %a@ :value %a@])"
              M.name N.pp n M.pp v);
        SI.CC.set_bitfield cc self.field_has_value true n;
        N_tbl.add self.values n v
      | None -> ()
    end;
    List.iter
      (fun (u,m_u) ->
        Log.debugf 20
          (fun k->k "(@[monoid[%s].on-new-term.sub@ :n %a@ :sub-t %a@ :value %a@])"
              M.name N.pp n T.pp u M.pp m_u);
        let n_u =
          try CC.find_t cc u
          with Not_found -> Error.errorf "subterm %a does not have a repr" T.pp u
        in
        if N.get_field self.field_has_value n_u then (
          let m_u' =
            try N_tbl.find self.values n_u
            with Not_found ->
              Error.errorf "node %a has bitfield but no value" N.pp n_u
          in
          match M.merge cc n_u m_u n_u m_u' (Expl.mk_list []) with
          | Error expl ->
            Error.errorf
              "when merging@ @[for node %a@],@ \
               values %a and %a:@ conflict %a"
              N.pp n_u M.pp m_u M.pp m_u' CC.Expl.pp expl
          | Ok m_u_merged ->
            Log.debugf 20
              (fun k->k "(@[monoid[%s].on-new-term.sub.merged@ \
                         :n %a@ :sub-t %a@ :value %a@])"
                  M.name N.pp n T.pp u M.pp m_u_merged);
            N_tbl.add self.values n_u m_u_merged;
        ) else (
          (* just add to [n_u] *)
          SI.CC.set_bitfield cc self.field_has_value true n_u;
          N_tbl.add self.values n_u m_u;
        )
      )
      l;
    ()

  let iter_all (self:t) : _ Iter.t =
    N_tbl.to_iter self.values

  let on_pre_merge (self:t) cc acts n1 n2 e_n1_n2 : unit =
    begin match get self n1, get self n2 with
      | Some v1, Some v2 ->
        Log.debugf 5
          (fun k->k
              "(@[monoid[%s].on_pre_merge@ (@[:n1 %a@ :val1 %a@])@ (@[:n2 %a@ :val2 %a@])@])"
              M.name N.pp n1 M.pp v1 N.pp n2 M.pp v2);
        begin match M.merge cc n1 v1 n2 v2 e_n1_n2 with
          | Ok v' ->
            N_tbl.remove self.values n2; (* only keep repr *)
            N_tbl.add self.values n1 v';
          | Error expl -> SI.CC.raise_conflict_from_expl cc acts expl
        end
      | None, Some cr ->
        SI.CC.set_bitfield cc self.field_has_value true n1;
        N_tbl.add self.values n1 cr;
        N_tbl.remove self.values n2; (* only keep reprs *)
      | Some _, None -> () (* already there on the left *)
      | None, None -> ()
    end

  let pp out (self:t) : unit =
    let pp_e out (t,v) = Fmt.fprintf out "(@[%a@ :has %a@])" N.pp t M.pp v in
    Fmt.fprintf out "(@[%a@])" (Fmt.iter pp_e) (iter_all self)

  let create_and_setup ?size (solver:SI.t) : t =
    let field_has_value =
      SI.CC.allocate_bitfield ~descr:("monoid."^M.name^".has-value")
        (SI.cc solver) in
    let self = { values=N_tbl.create ?size (); field_has_value; } in
    SI.on_cc_new_term solver (on_new_term self);
    SI.on_cc_pre_merge solver (on_pre_merge self);
    self
end
