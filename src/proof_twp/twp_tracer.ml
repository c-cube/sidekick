(** Proof tracer that emits .twp proof files directly.

    Implements Sidekick_smt_solver.Tracer.t:
    - Proof.Tracer.t methods: capture proof steps and emit .twp lines
    - Sidekick_sat.Tracer.t methods: no-ops (we don't trace SAT)
    - emit_assert_term: no-op
*)

module Proof = Sidekick_proof
module Sat_tracer = Sidekick_sat.Tracer
module Smt_tracer = Sidekick_smt_solver.Tracer
open Twp_state

(** Create a Smt_tracer.t that emits .twp proof steps into [state]. *)
let create (state : Twp_state.t) : Smt_tracer.t =
  Twp_state.emit_preamble state;
  let next_step_id = ref 1 in
  object
    val mutable enabled = true

    (* Term.Tracer.t *)
    method emit_term (_t : Term.t) : Term.Tracer.term_ref =
      Sidekick_trace.Entry_id.dummy

    (* Proof.Tracer.t *)
    method proof_enabled = enabled
    method proof_enable b = enabled <- b

    method emit_proof_step (p : Proof.Pterm.delayed) : Proof.Step.id =
      if not enabled then
        Proof.Step.dummy
      else (
        let pt = p () in
        let sid = !next_step_id in
        next_step_id := sid + 1;
        let step_id = Sidekick_trace.Entry_id.of_int_unsafe sid in
        let p_idx = Twp_pterm.emit_pterm state pt in
        Hashtbl.replace state.step_tbl sid p_idx;
        step_id
      )

    method emit_proof_delete _id = ()

    (* Sidekick_sat.Tracer.t — no-ops *)
    method sat_assert_clause ~id:_ _ _ = Sidekick_trace.Entry_id.dummy
    method sat_delete_clause ~id:_ _ = ()
    method sat_unsat_clause ~id:_ = Sidekick_trace.Entry_id.dummy
    method sat_encode_lit _ = Ser_value.null

    (* Smt_tracer.t extra method *)
    method emit_assert_term _ = Sidekick_trace.Entry_id.dummy
  end
