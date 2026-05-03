(** Minidag proof emission for sidekick.

    Provides a [Sidekick_smt_solver.Tracer.t] that writes a granite-compatible
    minidag proof stream to a file (extension [.granite]). *)

module Term_encoder = Term_encoder
module Proof_encoder = Proof_encoder
module Minidag_tracer = Minidag_tracer

let create_tracer = Minidag_tracer.create
let open_file = Minidag_tracer.open_file
