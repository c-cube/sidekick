(** Main types and signatures *)

(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

open Sidekick_core

(** Solver in a "SATISFIABLE" state *)
module type SAT_STATE = sig
  val eval : Lit.t -> bool
  (** Returns the valuation of a lit in the current state
      of the sat solver.
      @raise UndecidedLit if the literal is not decided *)

  val eval_level : Lit.t -> bool * int
  (** Return the current assignement of the literals, as well as its
      decision level. If the level is 0, then it is necessary for
      the literal to have this value; otherwise it is due to choices
      that can potentially be backtracked.
      @raise UndecidedLit if the literal is not decided *)

  val iter_trail : (Lit.t -> unit) -> unit
  (** Iter through the lits in order of decision/propagation
      (starting from the first propagation, to the last propagation). *)
end

type sat_state = (module SAT_STATE)
(** The type of values returned when the solver reaches a SAT state. *)

(** Solver in an "UNSATISFIABLE" state *)
module type UNSAT_STATE = sig
  type clause

  val unsat_conflict : unit -> clause
  (** Returns the unsat clause found at the toplevel *)

  val unsat_assumptions : unit -> Lit.t Iter.t
  (** Subset of assumptions responsible for "unsat" *)

  val unsat_proof : unit -> Proof_term.step_id
end

type 'clause unsat_state = (module UNSAT_STATE with type clause = 'clause)
(** The type of values returned when the solver reaches an UNSAT state. *)

type same_sign = bool
(** This type is used during the normalisation of lits.
    [true] means the literal stayed the same, [false] that its sign was flipped. *)

(** The type of reasons for propagations of a lit [f]. *)
type reason = Consequence of (unit -> Lit.t list * Proof_step.id) [@@unboxed]
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

let pp_lbool out = function
  | L_true -> Fmt.string out "true"
  | L_false -> Fmt.string out "false"
  | L_undefined -> Fmt.string out "undefined"

(** Actions available to the Plugin.

    The plugin provides callbacks for the SAT solver to use. These callbacks
    are provided with a [(module ACTS)] so they can modify the SAT solver
    by adding new lemmas, raise conflicts, etc. *)
module type ACTS = sig
  val proof : Proof_trace.t

  val iter_assumptions : (Lit.t -> unit) -> unit
  (** Traverse the new assumptions on the boolean trail. *)

  val eval_lit : Lit.t -> lbool
  (** Obtain current value of the given literal *)

  val add_lit : ?default_pol:bool -> Lit.t -> unit
  (** Map the given lit to an internal atom, which will be decided by the
      SAT solver. *)

  val add_clause : ?keep:bool -> Lit.t list -> Proof_step.id -> unit
  (** Add a clause to the solver.
      @param keep if true, the clause will be kept by the solver.
        Otherwise the solver is allowed to GC the clause and propose this
        partial model again.
      - [C_use_allocator alloc] puts the clause in the given allocator.
  *)

  val raise_conflict : Lit.t list -> Proof_step.id -> 'b
  (** Raise a conflict, yielding control back to the solver.
      The list of atoms must be a valid theory lemma that is false in the
      current trail. *)

  val propagate : Lit.t -> reason -> unit
  (** Propagate a lit, i.e. the theory can evaluate the lit to be true
      (see the definition of {!type:eval_res} *)

  val add_decision_lit : Lit.t -> bool -> unit
  (** Ask the SAT solver to decide on the given lit with given sign
      before it can answer [SAT]. The order of decisions is still unspecified.
      Useful for theory combination. This will be undone on backtracking. *)
end

type acts = (module ACTS)
(** The type for a slice of assertions to assume/propagate in the theory. *)

(** Signature for theories to be given to the CDCL(T) solver *)
module type THEORY_CDCL_T = sig
  val push_level : unit -> unit
  (** Create a new backtrack level *)

  val pop_levels : int -> unit
  (** Pop [n] levels of the theory *)

  val partial_check : acts -> unit
  (** Assume the lits in the slice, possibly using the [slice]
      to push new lits to be propagated or to raising a conflict or to add
      new lemmas. *)

  val final_check : acts -> unit
  (** Called at the end of the search in case a model has been found.
      If no new clause is pushed, then proof search ends and "sat" is returned;
      if lemmas are added, search is resumed;
      if a conflict clause is added, search backtracks and then resumes. *)
end

module type PLUGIN = sig
  include THEORY_CDCL_T

  val has_theory : bool
  (** [true] iff the solver is parametrized by a theory, not just
      pure SAT. *)
end

type plugin = (module PLUGIN)
