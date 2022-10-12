open Sidekick_core
module Tr = Sidekick_trace
module Proof = Sidekick_proof

class type t =
  object
    inherit Proof.Tracer.t

    method sat_assert_clause :
      id:int -> Lit.t Iter.t -> Proof.Step.id -> Tr.Entry_id.t

    method sat_delete_clause : id:int -> Lit.t Iter.t -> unit
    method sat_unsat_clause : id:int -> Tr.Entry_id.t
    method sat_encode_lit : Lit.t -> Ser_value.t
  end

class dummy : t =
  object
    inherit Proof.Tracer.dummy
    method sat_assert_clause ~id:_ _ _ = Tr.Entry_id.dummy
    method sat_delete_clause ~id:_ _ = ()
    method sat_unsat_clause ~id:_ = Tr.Entry_id.dummy
    method sat_encode_lit _ = Ser_value.null
  end

let dummy : t = new dummy

let assert_clause (self : #t) ~id c p : Tr.Entry_id.t =
  self#sat_assert_clause ~id c p

let assert_clause' (self : #t) ~id c p : unit =
  ignore (self#sat_assert_clause ~id c p : Tr.Entry_id.t)

let unsat_clause (self : #t) ~id : Tr.Entry_id.t = self#sat_unsat_clause ~id

let unsat_clause' (self : #t) ~id : unit =
  ignore (self#sat_unsat_clause ~id : Tr.Entry_id.t)

let delete_clause (self : #t) ~id c = self#sat_delete_clause ~id c
let encode_lit (self : #t) lit = self#sat_encode_lit lit
