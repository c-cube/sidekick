open Sidekick_core
module Tr = Sidekick_trace

type Tr.entry_view += Assert of Term.t | Assert_clause of Lit.t list

class type t =
  object
    inherit Term.Tracer.t

    method emit_assert_term : Term.t -> Tr.Entry_id.t
    (** Emit an assertion *)

    method emit_assert_clause : Lit.t list -> Tr.Entry_id.t
    (** Emit an assertion *)
  end

class dummy : t
(** Dummy tracer *)

class concrete : Tr.Sink.t -> t
(** Tracer emitting to a sink *)

val dummy : t
val concrete : sink:Tr.Sink.t -> t
val assert_term : #t -> Term.t -> Tr.Entry_id.t
val assert_term' : #t -> Term.t -> unit
val assert_clause : #t -> Lit.t list -> Tr.Entry_id.t
val assert_clause' : #t -> Lit.t list -> unit
val assert_clause_arr' : #t -> Lit.t array -> unit
