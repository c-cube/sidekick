(** Tracer for clauses and literals *)

module Tr = Sidekick_trace

(** Tracer for clauses. *)
class type t =
  object
    method assert_clause : id:int -> Lit.t Iter.t -> Tr.Entry_id.t
    method delete_clause : id:int -> Lit.t Iter.t -> unit
    method unsat_clause : id:int -> Tr.Entry_id.t
    method encode_lit : Lit.t -> Ser_value.t
  end

class dummy : t

val dummy : t
(** Dummy tracer, recording nothing. *)

val assert_clause : #t -> id:int -> Lit.t Iter.t -> Tr.Entry_id.t
val assert_clause' : #t -> id:int -> Lit.t Iter.t -> unit
val delete_clause : #t -> id:int -> Lit.t Iter.t -> unit
val unsat_clause : #t -> id:int -> Tr.Entry_id.t
val unsat_clause' : #t -> id:int -> unit
val encode_lit : #t -> Lit.t -> Ser_value.t
