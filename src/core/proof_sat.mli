(** SAT-solver proof emission. *)

open Proof_term

type lit = Lit.t

val sat_input_clause : lit Iter.t -> Proof_term.t
(** Emit an input clause. *)

val sat_redundant_clause : lit Iter.t -> hyps:step_id Iter.t -> Proof_term.t
(** Emit a clause deduced by the SAT solver, redundant wrt previous clauses.
    The clause must be RUP wrt [hyps]. *)

val sat_unsat_core : lit Iter.t -> Proof_term.t
(** TODO: is this relevant here? *)
