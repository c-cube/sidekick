(** Emit terms in traces.

  Traces will contains terms, encoded as a DAG. Each subterm is its own
  event, and gets a term identifier used in other subsequent entries
  to refer to it.
*)

open Sidekick_core_logic
module Tr = Sidekick_trace

type Tr.entry_view += private Def_term of { id: int }
type t

val create : sink:Tr.Sink.t -> unit -> t
val emit : t -> Term.t -> Tr.Entry_id.t
