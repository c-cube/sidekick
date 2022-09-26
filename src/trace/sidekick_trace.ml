(** Tracing.

    Sidekick should be able to emit traces of some or all of the events
    happening inside its components (SAT solver, SMT solver, theories,
    etc.).

    Traces can be written to disk and read back later from another
    process.

    The two initial intended use cases are:

      - proof production (trace all inferences; reconstruct a proof from them
        starting from the inference of [false])
      - debugging (trace some inferences/internal states/partial models;
        double check them later)

*)

(** {2 Exports} *)

module Entry_view = Entry_view
module Entry_read = Entry_read
module Sink = Sink
module Source = Source
module Entry_id = Entry_id

type entry_id = Entry_id.t
type entry_view = Entry_view.t = ..
