
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

  let[@inline] map_view ~f_f ~f_t ~f_ts (v:_ t) : _ t =
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

  module Term : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    type state

    val bool : state -> bool -> t

    val cc_view : t -> (Fun.t, t, t Iter.t) CC_view.t
    (** View the term through the lens of the congruence closure *)
  end
end

module type TERM_LIT = sig
  include TERM

  module Lit : sig
    type t
    val neg : t -> t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    val sign : t -> bool
    val term : t -> Term.t
  end
end

module type CC_ARG = sig
  include TERM_LIT

  module Proof : sig
    type t
    val pp : t Fmt.printer

    val default : t
    (* TODO: to give more details
    val cc_lemma : unit -> t
       *)
  end

  module Ty : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  (** Monoid embedded in every node *)
  module Data : sig
    type t

    val empty : t

    val merge : t -> t -> t
  end

  module Actions : sig
    type t

    val raise_conflict : t -> Lit.t list -> 'a

    val propagate : t -> Lit.t -> reason:Lit.t Iter.t -> unit
  end

  (* TODO: instead, provide model as a `equiv_class Iter.t`, for the
     benefit of $whatever_theory_combination_method? 
  module Value : sig
    type t

    val pp : t Fmt.printer

    val fresh : Term.t -> t

    val true_ : t
    val false_ : t
  end

  module Model : sig
    type t

    val pp : t Fmt.printer

    val eval : t -> Term.t -> Value.t option
    (** Evaluate the term in the current model *)

    val add : Term.t -> Value.t -> t -> t
  end
     *)
end

module type CC_S = sig
  module A : CC_ARG
  type term_state = A.Term.state
  type term = A.Term.t
  type fun_ = A.Fun.t
  type lit = A.Lit.t
  type proof = A.Proof.t
  type th_data = A.Data.t
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

    val th_data : t -> th_data
    (** Access theory data for this node *)

    val get_field_usr1 : t -> bool
    val set_field_usr1 : t -> bool -> unit

    val get_field_usr2 : t -> bool
    val set_field_usr2 : t -> bool -> unit
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

  type conflict = lit list

  (** Accessors *)

  val term_state : t -> term_state

  val find : t -> node -> repr
  (** Current representative *)

  val add_term : t -> term -> node
  (** Add the term to the congruence closure, if not present already.
      Will be backtracked. *)

  module Theory : sig
    type cc = t

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
  end

  type ev_on_merge = t -> N.t -> th_data -> N.t -> th_data -> Expl.t -> unit
  type ev_on_new_term = t -> N.t -> term -> th_data -> th_data option

  val create :
    ?stat:Stat.t ->
    ?on_merge:ev_on_merge list ->
    ?on_new_term:ev_on_new_term list ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure. *)

  val on_merge : t -> ev_on_merge -> unit
  (** Add a function to be called when two classes are merged *)

  val on_new_term : t -> ev_on_new_term -> unit
  (** Add a function to be called when a new node is created *)

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
    val check_invariants : t -> unit
    val pp : t Fmt.printer
  end
  (**/**)
end

type ('model, 'proof, 'ucore, 'unknown) solver_res =
  | Sat of 'model
  | Unsat of {
      proof: 'proof option;
      unsat_core: 'ucore;
    }
  | Unknown of 'unknown

module type SOLVER = sig
  module A : CC_ARG
  module CC : CC_S with module A = A

  type ty = A.Ty.t
  type lit = A.Lit.t
  type term = A.Term.t
  type term_state = A.Term.state
  type proof = A.Proof.t

  (** Unsatisfiable conjunction.
      Its negation will become a conflict clause *)
  type conflict = lit list

  (** {3 Actions available to some of the theory's callbacks} *)
  module type ACTIONS = sig
    val cc : CC.t

    val raise_conflict: conflict -> 'a
    (** Give a conflict clause to the solver *)

    val propagate: lit -> (unit -> lit list) -> unit
    (** Propagate a boolean using a unit clause.
        [expl => lit] must be a theory lemma, that is, a T-tautology *)

    val propagate_l: lit -> lit list -> unit
    (** Propagate a boolean using a unit clause.
        [expl => lit] must be a theory lemma, that is, a T-tautology *)

    val add_lit : lit -> unit
    (** Add the given literal to the SAT solver, so it gets assigned
        a boolean value *)

    val add_local_axiom: lit list -> unit
    (** Add local clause to the SAT solver. This clause will be
        removed when the solver backtracks. *)

    val add_persistent_axiom: lit list -> unit
    (** Add toplevel clause to the SAT solver. This clause will
        not be backtracked. *)
  end

  type actions = (module ACTIONS)

  (** {3 Main type for a solver} *)
  type t

  type solver = t

  (** {3 A theory's state} *)
  module type THEORY = sig
    type t

    val name : string
    (** Name of the theory *)

    val create : term_state -> t
    (** Instantiate the theory's state for the given solver, and
        register to callbacks, etc. *)

    val setup: t -> solver -> unit
    (** Setup the theory for the given solver, register callbacks, etc. *)

    val push_level : t -> unit

    val pop_levels : t -> int -> unit
  end

  type theory = (module THEORY)

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
  end

  (** {3 Boolean Atoms} *)
  module Atom : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t CCFormat.printer
  end

  (** {3 Main API} *)

  val cc : t -> CC.t
  val stats : t -> Stat.t
  val tst : t -> term_state

  val on_partial_check : t -> (actions -> lit Iter.t -> unit) -> unit
  (** Called with the slice of literals newly added on the trail *)

  val on_final_check: t -> (actions -> lit Iter.t -> unit) -> unit
  (** Final check, must be complete (i.e. must raise a conflict
      if the set of literals is not satisfiable) *)

  val create :
    ?stat:Stat.t ->
    ?size:[`Big | `Tiny | `Small] ->
    (* TODO? ?config:Config.t -> *)
    ?store_proof:bool ->
    theories:theory list ->
    unit -> t

  val add_theory : t -> theory -> unit
  (** Add a theory to the solver *)

  val mk_atom_lit : t -> lit -> Atom.t

  val mk_atom_t : t -> ?sign:bool -> term -> Atom.t

  val add_clause_lits : t -> lit IArray.t -> unit

  val add_clause_lits_l : t -> lit list -> unit

  val add_clause : t -> Atom.t IArray.t -> unit

  val add_clause_l : t -> Atom.t list -> unit

  type res = (Model.t, proof, lit IArray.t, Unknown.t) solver_res
  (** Result of solving for the current set of clauses *)

  val solve :
    ?on_exit:(unit -> unit) list ->
    ?check:bool ->
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

  (* TODO?
  val on_mk_model : t -> (lit Iter.t -> Model.t -> Model.t) -> unit
  (** Update the given model *)
    *)

  (* TODO: remove?
  let make
    (type st)
      ?(check_invariants=fun _ -> ())
      ?(on_new_term=fun _ _ _ -> ())
      ?(on_merge=fun _ _ _ _ _ -> ())
      ?(partial_check=fun _ _ _ -> ())
      ?(mk_model=fun _ _ m -> m)
      ?(push_level=fun _ -> ())
      ?(pop_levels=fun _ _ -> ())
      ?(cc_th=fun _->[])
      ~name
      ~final_check
      ~create
      () : t =
    let module A = struct
      type nonrec t = st
      let name = name
      let create = create
      let on_new_term = on_new_term
      let on_merge = on_merge
      let partial_check = partial_check
      let final_check = final_check
      let mk_model = mk_model
      let check_invariants = check_invariants
      let push_level = push_level
      let pop_levels = pop_levels
      let cc_th = cc_th
    end in
    (module A : S)

  type unknown =
    | U_timeout
    | U_incomplete

  val pp_unknown : unknown CCFormat.printer

  *)

  (**/**)
  module Debug_ : sig
    val on_check_invariants : t -> (unit -> unit) -> unit
    val check_model : t -> unit
  end
  (**/**)
end
