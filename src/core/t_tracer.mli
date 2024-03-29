(** Emit terms in traces.

  Traces will contains terms, encoded as a DAG. Each subterm is its own
  event, and gets a term identifier used in other subsequent entries
  to refer to it.
*)

open Sidekick_core_logic
module Tr = Sidekick_trace

type term_ref = T_ref.t

class type t =
  object
    method emit_term : Term.t -> term_ref
  end

(** Dummy implementation, returns {!Tr.Entry_id.dummy} *)
class dummy :
  object
    inherit t
    method emit_term : Term.t -> term_ref
  end

class concrete : sink:Tr.Sink.t -> t
(** Concrete implementation of [t] *)

val create : sink:Tr.Sink.t -> unit -> t
(** [create ~sink ()] makes a tracer that will write terms
    into the given sink. *)

val emit : #t -> Term.t -> term_ref
val emit' : #t -> Term.t -> unit
