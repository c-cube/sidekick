module Tr = Sidekick_trace

type step_id = Step.id

class type t =
  object
    inherit Term.Tracer.t
    method proof_enabled : bool
    method proof_enable : bool -> unit
    method emit_proof_step : Pterm.delayed -> step_id
    method emit_proof_delete : step_id -> unit
  end

let[@inline] enabled (self : #t) : bool = self#proof_enabled
let[@inline] enable (self : #t) (b : bool) : unit = self#proof_enable b
let[@inline] add_step (self : #t) rule : step_id = self#emit_proof_step rule
let[@inline] delete (self : #t) s : unit = self#emit_proof_delete s
let dummy_step_id : step_id = Sidekick_trace.Entry_id.dummy

class dummy : t =
  object
    inherit Term.Tracer.dummy
    method proof_enabled = false
    method proof_enable _ = ()
    method emit_proof_step _ = dummy_step_id
    method emit_proof_delete _ = ()
  end

let dummy : t = new dummy

class concrete ~sink : t =
  object (self)
    val mutable enabled = true
    inherit Term.Tracer.concrete ~sink
    method proof_enabled = enabled
    method proof_enable b = enabled <- b

    method emit_proof_delete id : unit =
      if enabled then Tr.Sink.emit' sink ~tag:"Pd" (Ser_value.int id)

    method emit_proof_step (p : Pterm.delayed) : step_id =
      if enabled then (
        let pt = p () in
        match pt with
        | Pterm.P_ref step when Step.equal step Step.dummy ->
          (* special shortcut: [Ref dummy] is not emitted,
             but just returns [dummy] *)
          Step.dummy
        | _ ->
          let v = Pterm.to_ser (self :> Term.Tracer.t) pt in
          Tr.Sink.emit sink ~tag:"Pt" v
      ) else
        Step.dummy
  end
