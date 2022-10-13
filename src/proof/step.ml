type id = Sidekick_trace.Entry_id.t

let equal (a : id) (b : id) = a = b
let dummy : id = Sidekick_trace.Entry_id.dummy
let pp : id Fmt.printer = Fmt.int
