
(** {1 Tracing Event Format}

    A nice profiling format based on json, useful for visualizing what goes on.
    It provides a backend for {!Sidekick_util.Profile} so that
    profiling probes will emit TEF events.

    Profiling is enabled if {!setup} is called, and if
    the environment variable "TEF" is set to "1" or "true".
    The trace is emitted in the file "trace.json.gz" in the directory
    where the solver is launched; you can open it in
    chrome/chromium at "chrome://tracing".

    {{: https://github.com/wolfpld/tracy} Tracy} can import (uncompressed)
    trace files with a nice native trace explorer.

    See {{: https://docs.google.com/document/d/1CvAClvFfyA5R-PhYUmn5OOQtYMH4h6I0nSsKchNAySU/}
          the documentation of TEF}
*)

val setup : unit -> unit
(** Install the TEF logger as a profiling backend. *)

val teardown : unit -> unit
