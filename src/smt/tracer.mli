(** Tracer for SMT solvers.

  The tracer is used to track clauses and terms used or deduced during proof
  search. *)

open Sidekick_core
module Tr = Sidekick_trace
module Proof = Sidekick_proof

class type t =
  object
    inherit Term.Tracer.t
    inherit Sidekick_sat.Tracer.t
    inherit Sidekick_proof.Tracer.t

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

val assert_clause :
  #t -> id:int -> Lit.t Iter.t -> Proof.Step.id -> Tr.Entry_id.t

val assert_clause' : #t -> id:int -> Lit.t Iter.t -> Proof.Step.id -> unit
val delete_clause : #t -> id:int -> Lit.t Iter.t -> unit
val unsat_clause : #t -> id:int -> Tr.Entry_id.t
val unsat_clause' : #t -> id:int -> unit
val encode_lit : #t -> Lit.t -> Ser_value.t
