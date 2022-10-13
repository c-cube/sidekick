open Sidekick_core
module Tr = Sidekick_trace
module Dec = Ser_decode

type step_id = Step.id
type t

val create : src:Tr.Source.t -> Term.Trace_reader.t -> t

val read_step : ?fix:bool -> t -> step_id -> (Pterm.t, Dec.Error.t) result
(** Read a step from the source at the given step id, using the trace reader.
    @param fix if true, dereferences in a loop so the returned proof term is
    not a Ref. *)

val dec_step_id : ?fix:bool -> t -> Pterm.t Dec.t
(** Reads an integer, decodes the corresponding entry *)
