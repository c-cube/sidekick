(** Tracer for clauses and literals *)

open Sidekick_core
module Tr = Sidekick_trace
module Proof = Sidekick_proof

(** Tracer for the SAT solver. *)
class type t =
  object
    inherit Proof.Tracer.t

    method sat_assert_clause :
      id:int -> Lit.t Iter.t -> Proof.Step.id -> Tr.Entry_id.t

    method sat_delete_clause : id:int -> Lit.t Iter.t -> unit
    method sat_unsat_clause : id:int -> Tr.Entry_id.t
    method sat_encode_lit : Lit.t -> Ser_value.t
  end

class dummy : t

val dummy : t
(** Dummy tracer, recording nothing. *)

val assert_clause :
  #t -> id:int -> Lit.t Iter.t -> Proof.Step.id -> Tr.Entry_id.t

val assert_clause' : #t -> id:int -> Lit.t Iter.t -> Proof.Step.id -> unit
val delete_clause : #t -> id:int -> Lit.t Iter.t -> unit
val unsat_clause : #t -> id:int -> Tr.Entry_id.t
val unsat_clause' : #t -> id:int -> unit
val encode_lit : #t -> Lit.t -> Ser_value.t
