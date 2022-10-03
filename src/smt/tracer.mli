open Sidekick_core
module Tr = Sidekick_trace

class type t =
  object
    inherit Term.Tracer.t
    inherit Clause_tracer.t

    method emit_assert_term : Term.t -> Tr.Entry_id.t
    (** Emit an assertion *)
  end

class dummy : t
(** Dummy tracer *)

class concrete : Tr.Sink.t -> t
(** Tracer emitting to a sink *)

val dummy : t
val make : sink:Tr.Sink.t -> unit -> t
val assert_term : #t -> Term.t -> Tr.Entry_id.t
val assert_term' : #t -> Term.t -> unit
val assert_clause : #t -> id:int -> Lit.t Iter.t -> Tr.Entry_id.t
val assert_clause' : #t -> id:int -> Lit.t Iter.t -> unit
val delete_clause : #t -> id:int -> Lit.t Iter.t -> unit
val unsat_clause : #t -> id:int -> Tr.Entry_id.t
val unsat_clause' : #t -> id:int -> unit
val encode_lit : #t -> Lit.t -> Ser_value.t
