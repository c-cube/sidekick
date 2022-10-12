module Tr = Sidekick_trace

type step_id = Step.id

class type t =
  object
    method proof_enabled : bool
    method emit_proof_step : Pterm.delayed -> step_id
    method emit_proof_delete : step_id -> unit
  end

let[@inline] enabled (self : #t) : bool = self#proof_enabled
let[@inline] add_step (self : #t) rule : step_id = self#emit_proof_step rule
let[@inline] delete (self : #t) s : unit = self#emit_proof_delete s
let dummy_step_id : step_id = Sidekick_trace.Entry_id.dummy

class dummy : t =
  object
    method proof_enabled = false
    method emit_proof_step _ = dummy_step_id
    method emit_proof_delete _ = ()
  end

let dummy : t = new dummy

class concrete ~sink : t =
  object
    method proof_enabled = true

    method emit_proof_delete id : unit =
      Tr.Sink.emit' sink ~tag:"Pd" (Ser_value.int id)

    method emit_proof_step (p : Pterm.delayed) : step_id = assert false
    (* TODO *)
  end
