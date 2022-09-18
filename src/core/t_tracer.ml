open Sidekick_core_logic
module Tr = Sidekick_trace
module T = Term

type Tr.entry_view += private Def_term of { id: int }
type t = { sink: Tr.Sink.t; emitted: Tr.Entry_id.t T.Weak_map.t }

let create ~sink () : t = { sink; emitted = T.Weak_map.create 16 }
let emit (self : t) (t : T.t) : Tr.Entry_id.t = assert false
