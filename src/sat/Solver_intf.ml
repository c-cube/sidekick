(** Interface for Solvers

    This modules defines the safe external interface for solvers.
    Solvers that implements this interface can be obtained using the [Make]
    functor.
*)

(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

type 'a printer = Format.formatter -> 'a -> unit

(** Solver in a "SATISFIABLE" state *)
module type SAT_STATE = sig
  type lit
  (** Literals (signed boolean atoms) *)

  val eval : lit -> bool
  (** Returns the valuation of a lit in the current state
      of the sat solver.
      @raise UndecidedLit if the literal is not decided *)

  val eval_level : lit -> bool * int
  (** Return the current assignement of the literals, as well as its
      decision level. If the level is 0, then it is necessary for
      the literal to have this value; otherwise it is due to choices
      that can potentially be backtracked.
      @raise UndecidedLit if the literal is not decided *)

  val iter_trail : (lit -> unit) -> unit
  (** Iter through the lits in order of decision/propagation
      (starting from the first propagation, to the last propagation). *)
end

type 'form sat_state = (module SAT_STATE with type lit = 'form)
(** The type of values returned when the solver reaches a SAT state. *)

(** Solver in an "UNSATISFIABLE" state *)
module type UNSAT_STATE = sig
  type lit
  type clause
  type proof_step

  val unsat_conflict : unit -> clause
  (** Returns the unsat clause found at the toplevel *)

  val unsat_assumptions : unit -> lit Iter.t
  (** Subset of assumptions responsible for "unsat" *)

  val unsat_proof : unit -> proof_step
end

type ('lit, 'clause, 'proof_step) unsat_state =
  (module UNSAT_STATE
     with type lit = 'lit
      and type clause = 'clause
      and type proof_step = 'proof_step)
(** The type of values returned when the solver reaches an UNSAT state. *)

type same_sign = bool
(** This type is used during the normalisation of lits.
    [true] means the literal stayed the same, [false] that its sign was flipped. *)

(** The type of reasons for propagations of a lit [f]. *)
type ('lit, 'proof_step) reason =
  | Consequence of (unit -> 'lit list * 'proof_step)
[@@unboxed]
(** [Consequence (l, p)] means that the lits in [l] imply the propagated
      lit [f]. The proof should be a proof of the clause "[l] implies [f]".

      invariant: in [Consequence (fun () -> l,p)], all elements of [l] must be true in
      the current trail.

      {b note} on lazyiness: the justification is suspended (using [unit -> …])
      to avoid potentially costly computations that might never be used
      if this literal is backtracked without participating in a conflict.
      Therefore the function that produces [(l,p)] needs only be safe in
      trails (partial models) that are conservative extensions of the current
      trail.
      If the theory isn't robust w.r.t. extensions of the trail (e.g. if
      its internal state undergoes significant changes),
      it can be easier to produce the explanation eagerly when
      propagating, and then use [Consequence (fun () -> expl, proof)] with
      the already produced [(expl,proof)] tuple.
  *)

type lbool = L_true | L_false | L_undefined  (** Valuation of an atom *)

(** Actions available to the Plugin

    The plugin provides callbacks for the SAT solver to use. These callbacks
    are provided with a [(module ACTS)] so they can modify the SAT solver
    by adding new lemmas, raise conflicts, etc. *)
module type ACTS = sig
  type lit
  type proof
  type proof_step

  val proof : proof

  val iter_assumptions : (lit -> unit) -> unit
  (** Traverse the new assumptions on the boolean trail. *)

  val eval_lit : lit -> lbool
  (** Obtain current value of the given literal *)

  val add_lit : ?default_pol:bool -> lit -> unit
  (** Map the given lit to an internal atom, which will be decided by the
      SAT solver. *)

  val add_clause : ?keep:bool -> lit list -> proof_step -> unit
  (** Add a clause to the solver.
      @param keep if true, the clause will be kept by the solver.
        Otherwise the solver is allowed to GC the clause and propose this
        partial model again.
      - [C_use_allocator alloc] puts the clause in the given allocator.
  *)

  val raise_conflict : lit list -> proof_step -> 'b
  (** Raise a conflict, yielding control back to the solver.
      The list of atoms must be a valid theory lemma that is false in the
      current trail. *)

  val propagate : lit -> (lit, proof_step) reason -> unit
  (** Propagate a lit, i.e. the theory can evaluate the lit to be true
      (see the definition of {!type:eval_res} *)

  val add_decision_lit : lit -> bool -> unit
  (** Ask the SAT solver to decide on the given lit with given sign
      before it can answer [SAT]. The order of decisions is still unspecified.
      Useful for theory combination. This will be undone on backtracking. *)
end

type ('lit, 'proof, 'proof_step) acts =
  (module ACTS
     with type lit = 'lit
      and type proof = 'proof
      and type proof_step = 'proof_step)
(** The type for a slice of assertions to assume/propagate in the theory. *)

exception No_proof

module type LIT = sig
  (** lits *)

  type t
  (** The type of atomic lits over terms. *)

  val equal : t -> t -> bool
  (** Equality over lits. *)

  val hash : t -> int
  (** Hashing function for lits. Should be such that two lits equal according
      to {!val:Expr_intf.S.equal} have the same hash. *)

  val pp : t printer
  (** Printing function used among other thing for debugging.  *)

  val neg : t -> t
  (** Formula negation *)

  val norm_sign : t -> t * same_sign
  (** Returns a 'normalized' form of the lit, possibly same_sign
      (in which case return [false]).
      [norm] must be so that [a] and [neg a] normalise to the same lit,
      but one returns [false] and the other [true]. *)
end

module type PROOF_RULES = Sidekick_sigs_proof_sat.S

(** Signature for theories to be given to the CDCL(T) solver *)
module type PLUGIN_CDCL_T = sig
  type t
  (** The plugin state itself *)

  module Lit : LIT
  module Proof_trace : Sidekick_sigs_proof_trace.S

  module Proof_rules :
    PROOF_RULES
      with type lit = Lit.t
       and type rule = Proof_trace.A.rule
       and type step_id = Proof_trace.A.step_id

  val push_level : t -> unit
  (** Create a new backtrack level *)

  val pop_levels : t -> int -> unit
  (** Pop [n] levels of the theory *)

  val partial_check :
    t -> (Lit.t, Proof_trace.t, Proof_trace.A.step_id) acts -> unit
  (** Assume the lits in the slice, possibly using the [slice]
      to push new lits to be propagated or to raising a conflict or to add
      new lemmas. *)

  val final_check :
    t -> (Lit.t, Proof_trace.t, Proof_trace.A.step_id) acts -> unit
  (** Called at the end of the search in case a model has been found.
      If no new clause is pushed, then proof search ends and "sat" is returned;
      if lemmas are added, search is resumed;
      if a conflict clause is added, search backtracks and then resumes. *)
end

(** Signature for pure SAT solvers *)
module type PLUGIN_SAT = sig
  module Lit : LIT
  module Proof_trace : Sidekick_sigs_proof_trace.S

  module Proof_rules :
    PROOF_RULES
      with type lit = Lit.t
       and type rule = Proof_trace.A.rule
       and type step_id = Proof_trace.A.step_id
end

exception Resource_exhausted
(** Can be raised in a progress handler *)

(** The external interface implemented by safe solvers, such as the one
    created by the {!Solver.Make} and {!Mcsolver.Make} functors. *)
module type S = sig
  (** {2 Internal modules}
      These are the internal modules used, you should probably not use them
      if you're not familiar with the internals of mSAT. *)

  module Lit : LIT
  module Proof_trace : Sidekick_sigs_proof_trace.S

  type lit = Lit.t
  (** literals *)

  type clause
  type theory
  type proof_rule = Proof_trace.A.rule
  type proof_step = Proof_trace.A.step_id

  type proof_trace = Proof_trace.t
  (** A representation of a full proof *)

  type solver
  (** The main solver type. *)

  type store
  (** Stores atoms, clauses, etc. *)

  module Clause : sig
    type t = clause

    val equal : t -> t -> bool

    module Tbl : Hashtbl.S with type key = t

    val pp : store -> t printer
    (** Print the clause *)

    val short_name : store -> t -> string
    (** Short name for a clause. Unspecified *)

    val n_atoms : store -> t -> int

    val lits_iter : store -> t -> lit Iter.t
    (** Literals of a clause *)

    val lits_a : store -> t -> lit array
    (** Atoms of a clause *)

    val lits_l : store -> t -> lit list
    (** List of atoms of a clause *)
  end

  (** Proof rules for SAT solving *)
  module Proof_rules :
    PROOF_RULES
      with type lit = lit
       and type rule = proof_rule
       and type step_id = proof_step

  (** {2 Main Solver Type} *)

  type t = solver
  (** Main solver type, containing all state for solving. *)

  val create :
    ?stat:Stat.t ->
    ?size:[ `Tiny | `Small | `Big ] ->
    proof:proof_trace ->
    theory ->
    t
  (** Create new solver
      @param theory the theory
      @param the proof
      @param size the initial size of internal data structures. The bigger,
        the faster, but also the more RAM it uses. *)

  val theory : t -> theory
  (** Access the theory state *)

  val store : t -> store
  (** Store for the solver *)

  val stat : t -> Stat.t
  (** Statistics *)

  val proof : t -> proof_trace
  (** Access the inner proof *)

  val on_conflict : t -> (Clause.t, unit) Event.t
  val on_decision : t -> (lit, unit) Event.t
  val on_learnt : t -> (Clause.t, unit) Event.t
  val on_gc : t -> (lit array, unit) Event.t

  (** {2 Types} *)

  (** Result type for the solver *)
  type res =
    | Sat of lit sat_state
        (** Returned when the solver reaches SAT, with a model *)
    | Unsat of (lit, clause, proof_step) unsat_state
        (** Returned when the solver reaches UNSAT, with a proof *)

  exception UndecidedLit
  (** Exception raised by the evaluating functions when a literal
      has not yet been assigned a value. *)

  (** {2 Base operations} *)

  val assume : t -> lit list list -> unit
  (** Add the list of clauses to the current set of assumptions.
      Modifies the sat solver state in place. *)

  val add_clause : t -> lit list -> proof_step -> unit
  (** Lower level addition of clauses *)

  val add_clause_a : t -> lit array -> proof_step -> unit
  (** Lower level addition of clauses *)

  val add_input_clause : t -> lit list -> unit
  (** Like {!add_clause} but with the justification of being an input clause *)

  val add_input_clause_a : t -> lit array -> unit
  (** Like {!add_clause_a} but with justification of being an input clause *)

  (** {2 Solving} *)

  val solve : ?on_progress:(unit -> unit) -> ?assumptions:lit list -> t -> res
  (** Try and solves the current set of clauses.
      @param assumptions additional atomic assumptions to be temporarily added.
        The assumptions are just used for this call to [solve], they are
        not saved in the solver's state.
      @param on_progress regularly called during solving.
        Can raise {!Resource_exhausted}
        to stop solving.

      @raise Resource_exhausted if the on_progress handler raised it to stop
  *)

  (** {2 Evaluating and adding literals} *)

  val add_lit : t -> ?default_pol:bool -> lit -> unit
  (** Ensure the SAT solver handles this particular literal, ie add
      a boolean variable for it if it's not already there. *)

  val set_default_pol : t -> lit -> bool -> unit
  (** Set default polarity for the given boolean variable.
      Sign of the literal is ignored. *)

  val true_at_level0 : t -> lit -> bool
  (** [true_at_level0 a] returns [true] if [a] was proved at level0, i.e.
      it must hold in all models *)

  val eval_lit : t -> lit -> lbool
  (** Evaluate atom in current state *)

  (** {2 Assumption stack} *)

  val push_assumption : t -> lit -> unit
  (** Pushes an assumption onto the assumption stack. It will remain
      there until it's pop'd by {!pop_assumptions}. *)

  val pop_assumptions : t -> int -> unit
  (** [pop_assumptions solver n] removes [n] assumptions from the stack.
      It removes the assumptions that were the most
      recently added via {!push_assumptions}. *)

  (** Result returned by {!check_sat_propagations_only} *)
  type propagation_result =
    | PR_sat
    | PR_conflict of { backtracked: int }
    | PR_unsat of (lit, clause, proof_step) unsat_state

  val check_sat_propagations_only :
    ?assumptions:lit list -> t -> propagation_result
  (** [check_sat_propagations_only solver] uses the added clauses
      and local assumptions (using {!push_assumptions} and [assumptions])
      to quickly assess whether the context is satisfiable.
      It is not complete; calling {!solve} is required to get an accurate
      result.
      @returns either [Ok()] if propagation yielded no conflict, or [Error c]
        if a conflict clause [c] was found. *)
end
