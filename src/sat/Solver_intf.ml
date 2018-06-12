(** Interface for Solvers

    This modules defines the safe external interface for solvers.
    Solvers that implements this interface can be obtained using the [Make]
    functor in {!Solver} or {!Mcsolver}.
*)

module Var_fields = BitField.Make()
module C_fields = BitField.Make()

type 'a printer = Format.formatter -> 'a -> unit

type 'form sat_state = Sat_state of {
  eval: 'form -> bool;
  (** Returns the valuation of a formula in the current state
      of the sat solver.
      @raise UndecidedLit if the literal is not decided *)
  eval_level: 'form -> bool * int;
  (** Return the current assignement of the literals, as well as its
      decision level. If the level is 0, then it is necessary for
      the atom to have this value; otherwise it is due to choices
      that can potentially be backtracked.
      @raise UndecidedLit if the literal is not decided *)
  iter_trail : ('form -> unit) -> unit;
  (** Iter through the formulas and terms in order of decision/propagation
      (starting from the first propagation, to the last propagation). *)
}
(** The type of values returned when the solver reaches a SAT state. *)

type ('clause, 'proof) unsat_state = Unsat_state of {
  unsat_conflict : unit -> 'clause;
  (** Returns the unsat clause found at the toplevel *)
  get_proof : unit -> 'proof;
  (** returns a persistent proof of the empty clause from the Unsat result. *)
}
(** The type of values returned when the solver reaches an UNSAT state. *)

type 'clause export = {
  clauses: 'clause Vec.t;
}
(** Export internal state *)

(** The external interface implemented by safe solvers, such as the one
    created by the {!Solver.Make} and {!Mcsolver.Make} functors. *)
module type S = sig
  (** {2 Internal modules}
      These are the internal modules used, you should probably not use them
      if you're not familiar with the internals of mSAT. *)

  type formula
  (** The type of atoms given by the module argument for formulas.
      An atom is a user-defined atomic formula whose truth value is
      picked by Msat. *)


  type atom (** SAT solver literals *)

  type clause (** SAT solver clauses *)

  type theory (** user theory *)

  type proof
  (** Lazy type for proof trees. Proofs are persistent objects, and can be
      extended to proof nodes using functions defined later. *)

  type lemma (** A theory lemma, used to justify a theory conflict clause *)

  type premise =
    | Hyp
    | Lemma of lemma
    | Simplified of clause
    | History of clause list

  type t
  (** Main solver type, containing all state for solving. *)

  val create : ?size:[`Tiny|`Small|`Big] -> unit -> t
  (** Create new solver
      @param size the initial size of internal data structures. The bigger,
        the faster, but also the more RAM it uses. *)

  (** {2 Types} *)

  (** Result type for the solver *)
  type res =
    | Sat of formula sat_state (** Returned when the solver reaches SAT, with a model *)
    | Unsat of (clause,proof) unsat_state (** Returned when the solver reaches UNSAT, with a proof *)

  exception UndecidedLit
  (** Exception raised by the evaluating functions when a literal
      has not yet been assigned a value. *)

  (** {2 Base operations} *)

  val n_vars : t -> int

  val theory : t -> theory

  val assume : ?permanent:bool -> t -> ?tag:int -> formula list list -> unit
  (** Add the list of clauses to the current set of assumptions.
      Modifies the sat solver state in place.
      @param permanent if true, kept after backtracking (default true) *)

  val add_clause : permanent:bool -> t -> clause -> unit
  (** Lower level addition of clauses. See {!Clause} to create clauses.
      @param permanent if true, kept after backtracking *)

  val solve : t -> ?assumptions:formula list -> unit -> res
  (** Try and solves the current set of clauses.
      @param assumptions additional atomic assumptions to be temporarily added.
        The assumptions are just used for this call to [solve], they are
        not saved in the solver's state. *)

  val unsat_core : proof -> clause list
  (** Returns the unsat core of a given proof, ie a subset of all the added
      clauses that is sufficient to establish unsatisfiability. *)

  val true_at_level0 : t -> formula -> bool
  (** [true_at_level0 a] returns [true] if [a] was proved at level0, i.e.
      it must hold in all models *)

  val get_tag : clause -> int option
  (** Recover tag from a clause, if any *)

  (* FIXME
  val push : t -> unit
  (** Push a new save point. Clauses added after this call to [push] will
      be added as normal, but the corresponding call to [pop] will
      remove these clauses. *)

  val pop : t -> unit
  (** Return to last save point, discarding clauses added since last
      call to [push] *)
     *)

  val actions : t -> (formula,lemma) Theory_intf.actions
  (** Obtain actions *)

  val export : t -> clause export

  val check_model : t -> unit

  (** {2 Re-export some functions} *)

  type solver = t

  module Atom : sig
    type t = atom
    val is_pos : t -> bool
    val neg : t -> t
    val abs : t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val get_formula : t -> formula
    val is_true : t -> bool

    val dummy : t
    val make : solver -> formula -> t

    val pp : t printer
  end

  (** A module to manipulate proofs. *)
  module Proof : sig
    type t = proof

    type node = {
      conclusion : clause; (** The conclusion of the proof *)
      step : step; (** The reasoning step used to prove the conclusion *)
    }
    (** A proof can be expanded into a proof node, which show the first step of the proof. *)

    (** The type of reasoning steps allowed in a proof. *)
    and step =
      | Hypothesis
      (** The conclusion is a user-provided hypothesis *)
      | Assumption
      (** The conclusion has been locally assumed by the user *)
      | Lemma of lemma
      (** The conclusion is a tautology provided by the theory, with associated proof *)
      | Duplicate of proof * atom list
      (** The conclusion is obtained by eliminating multiple occurences of the atom in
          the conclusion of the provided proof. *)
      | Resolution of proof * proof * atom
      (** The conclusion can be deduced by performing a resolution between the conclusions
          of the two given proofs. The atom on which to perform the resolution is also given. *)

    exception Insufficient_hyps
    (** Raised when a complete resolution derivation cannot be found using the current hypotheses. *)

    (** {3 Proof building functions} *)

    val prove : clause -> t
    (** Given a clause, return a proof of that clause.
        @raise Insuficient_hyps if it does not succeed. *)

    val prove_atom : atom -> t option
    (** Given an atom [a], returns a proof of the clause [[a]] if [a] is true at level 0 *)

    (** {3 Proof Nodes} *)

    val is_leaf : step -> bool
    (** Returns wether the the proof node is a leaf, i.e. an hypothesis,
        an assumption, or a lemma.
        [true] if and only if {parents} returns the empty list. *)

    val expl : step -> string
    (** Returns a short string description for the proof step; for instance
        ["hypothesis"] for a [Hypothesis]
        (it currently returns the variant name in lowercase). *)

    val parents : step -> t list
    (** Returns the parents of a proof node. *)

    (** {3 Proof Manipulation} *)

    val expand : proof -> node
    (** Return the proof step at the root of a given proof. *)

    val step : proof -> step

    val conclusion : proof -> clause
    (** What is proved at the root of the clause *)

    val fold : ('a -> node -> 'a) -> 'a -> t -> 'a
    (** [fold f acc p], fold [f] over the proof [p] and all its node. It is guaranteed that
        [f] is executed exactly once on each proof node in the tree, and that the execution of
        [f] on a proof node happens after the execution on the parents of the nodes. *)

    val unsat_core : t -> clause list
    (** Returns the unsat_core of the given proof, i.e the lists of conclusions
        of all leafs of the proof.
        More efficient than using the [fold] function since it has
        access to the internal representation of proofs *)

    (** {3 Misc} *)

    val check : t -> unit
    (** Check the contents of a proof. Mainly for internal use *)

    module Tbl : Hashtbl.S with type key = t
  end

  module Clause : sig
    type t = clause

    val atoms : t -> atom array (** do not modify *)
    val atoms_l : t -> atom list
    val forms : t -> formula IArray.t
    val forms_l : t -> formula list
    val tag : t -> int option
    val equal : t -> t -> bool

    val make : ?tag:int -> atom array -> t
    (** Make a clause from this array of SAT literals.
        The array's ownership is transferred to the clause, do not mutate it *)

    val make_l : ?tag:int -> atom list -> t

    val of_formulas : solver -> ?tag:int -> formula list -> t

    val premise : t -> premise
    val is_learnt : t -> bool

    val name : t -> string
    val pp : t printer
    val pp_dimacs : t printer

    val dummy : t

    module Tbl : Hashtbl.S with type key = t
  end

  module Formula : sig
    type t = formula
    val pp : t printer
  end
end

