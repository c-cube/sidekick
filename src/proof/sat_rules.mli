(** SAT-solver proof emission. *)

type lit = Lit.t

val sat_input_clause : lit list -> Pterm.t
(** Emit an input clause. *)

val sat_redundant_clause : lit list -> hyps:Step.id Iter.t -> Pterm.t
(** Emit a clause deduced by the SAT solver, redundant wrt previous clauses.
    The clause must be RUP wrt [hyps]. *)

val sat_unsat_core : lit list -> Pterm.t
(** TODO: is this relevant here? *)
