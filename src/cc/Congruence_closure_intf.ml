
(** {1 Types used by the congruence closure} *)

type ('f, 't, 'ts) view =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 'ts
  | If of 't * 't * 't
  | Eq of 't * 't
  | Not of 't
  | Opaque of 't (* do not enter *)

let[@inline] map_view ~f_f ~f_t ~f_ts (v:_ view) : _ view =
  match v with
  | Bool b -> Bool b
  | App_fun (f, args) -> App_fun (f_f f, f_ts args)
  | App_ho (f, args) -> App_ho (f_t f, f_ts args)
  | Not t -> Not (f_t t)
  | If (a,b,c) -> If (f_t a, f_t b, f_t c)
  | Eq (a,b) -> Eq (f_t a, f_t b)
  | Opaque t -> Opaque (f_t t)

let iter_view ~f_f ~f_t ~f_ts (v:_ view) : unit =
  match v with
  | Bool _ -> ()
  | App_fun (f, args) -> f_f f; f_ts args
  | App_ho (f, args) -> f_t f; f_ts args
  | Not t -> f_t t
  | If (a,b,c) -> f_t a; f_t b; f_t c;
  | Eq (a,b) -> f_t a; f_t b
  | Opaque t -> f_t t

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

    (** View the term through the lens of the congruence closure *)
    val cc_view : t -> (Fun.t, t, t Iter.t) view
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

module type ARG = sig
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

  (** Monoid embedded in every node *)
  module Data : sig
    type t

    val empty : t

    val merge : t -> t -> t
  end
end

module type S = sig
  type term_state
  type term
  type fun_
  type lit
  type proof
  type model
  type th_data

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

  (** Actions available to the theory *)
  type sat_actions = (Msat.void, lit, Msat.void, proof) Msat.acts

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
