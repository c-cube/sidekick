(** SMT tracer that writes proof steps as a minidag byte stream.

    Implements [Sidekick_smt_solver.Tracer.t]. The output file uses the
    [.granite] extension and contains a sequence of minidag nodes: first term
    nodes, then proof nodes. The last proof node is the root (empty clause). *)

module Proof = Sidekick_proof
module Smt_tracer = Sidekick_smt_solver.Tracer
module E = Sidekick_minidag.Encode

class oc_output (oc : out_channel) : E.output =
  object
    method write buf pos len = output_bytes oc (Bytes.sub buf pos len)
  end

let create ~(oc : out_channel) ~(tst : Term.store) () : Smt_tracer.t =
  let enc = E.create ~out:(new oc_output oc) () in
  let te = Term_encoder.create enc in
  let pe = Proof_encoder.create te tst in
  at_exit (fun () ->
      (try E.flush enc with _ -> ());
      try close_out oc with _ -> ());
  object
    val mutable enabled = true
    method proof_enabled = enabled
    method proof_enable b = enabled <- b

    method emit_proof_step (p : Proof.Pterm.delayed) : Proof.Step.id =
      if not enabled then
        Proof.Step.dummy
      else (
        (* The step id IS the minidag byte offset of the emitted node. *)
        let off = Proof_encoder.emit_step pe Proof.Step.dummy p in
        Sidekick_trace.Entry_id.of_int_unsafe (off :> int)
      )

    method emit_proof_delete _id = ()
    method emit_term (_t : Term.t) = Sidekick_trace.Entry_id.dummy
    method sat_assert_clause ~id:_ _ _ = Sidekick_trace.Entry_id.dummy
    method sat_delete_clause ~id:_ _ = ()
    method sat_unsat_clause ~id:_ = Sidekick_trace.Entry_id.dummy
    method sat_encode_lit _ = Ser_value.null
    method emit_assert_term _ = Sidekick_trace.Entry_id.dummy
  end

(** Open [path] and return a tracer writing a minidag proof to it. *)
let open_file ~path ~tst () : Smt_tracer.t =
  create ~oc:(open_out_bin path) ~tst ()
