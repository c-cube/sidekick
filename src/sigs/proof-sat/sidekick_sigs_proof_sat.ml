(** Signature for SAT-solver proof emission. *)
module type S = sig
  type rule
  (** The stored proof (possibly nil, possibly on disk, possibly in memory) *)

  type step_id
  (** identifier for a proof *)

  type lit
  (** A boolean literal for the proof trace *)

  val sat_input_clause : lit Iter.t -> rule
  (** Emit an input clause. *)

  val sat_redundant_clause : lit Iter.t -> hyps:step_id Iter.t -> rule
  (** Emit a clause deduced by the SAT solver, redundant wrt previous clauses.
      The clause must be RUP wrt [hyps]. *)

  (* FIXME: goes in proof trace itself? not exactly a rule…
     val sat_unsat_core : lit Iter.t -> rule
     (** Produce a proof of the empty clause given this subset of the assumptions.
         FIXME: probably needs the list of proof_step that disprove the lits? *)
  *)
end
