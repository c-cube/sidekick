open Sidekick_core
module Tr = Sidekick_trace
module Proof = Sidekick_proof
module V = Ser_value

class type t =
  object
    inherit Term.Tracer.t
    inherit Sidekick_proof.Tracer.t
    inherit Sidekick_sat.Tracer.t
    method emit_assert_term : Term.t -> Tr.Entry_id.t
  end

class concrete (sink : Tr.Sink.t) : t =
  object (self)
    inherit Sidekick_proof.Tracer.concrete ~sink as p_tracer

    method emit_assert_term t =
      let id_t = p_tracer#emit_term t in
      let v = V.int id_t in
      let id = Tr.Sink.emit sink ~tag:"AssT" v in
      id

    method sat_encode_lit (lit : Lit.t) : V.t =
      let sign = Lit.sign lit in
      let id_t = p_tracer#emit_term @@ Lit.term lit in
      V.(list [ bool sign; int id_t ])

    method sat_assert_clause ~id (c : Lit.t Iter.t) (pr : Proof.Step.id) =
      (* get a list of pairs *)
      let l = Iter.map self#sat_encode_lit c |> Iter.to_rev_list |> V.list in
      let v = V.(dict_of_list [ "id", int id; "c", l; "p", int pr ]) in
      let id = Tr.Sink.emit sink ~tag:"AssC" v in
      id

    method sat_unsat_clause ~id =
      let v = Ser_value.(dict_of_list [ "id", int id ]) in
      Tr.Sink.emit sink ~tag:"UnsatC" v

    method sat_delete_clause ~id _lits : unit =
      let v = Ser_value.(dict_of_list [ "id", int id ]) in
      ignore (Tr.Sink.emit sink ~tag:"DelCSat" v : Tr.Entry_id.t)
  end

class dummy : t =
  object
    inherit Term.Tracer.dummy
    inherit Sidekick_sat.Tracer.dummy
    method emit_assert_term _ = Tr.Entry_id.dummy
  end

let dummy : #t = new dummy
let make ~sink () = new concrete sink

let assert_clause (self : #t) ~id c pr : Tr.Entry_id.t =
  self#sat_assert_clause ~id c pr

let assert_clause' (self : #t) ~id c pr : unit =
  ignore (self#sat_assert_clause ~id c pr : Tr.Entry_id.t)

let unsat_clause (self : #t) ~id : Tr.Entry_id.t = self#sat_unsat_clause ~id

let unsat_clause' (self : #t) ~id : unit =
  ignore (self#sat_unsat_clause ~id : Tr.Entry_id.t)

let delete_clause (self : #t) ~id c = self#sat_delete_clause ~id c
let encode_lit (self : #t) lit = self#sat_encode_lit lit
let assert_term (self : #t) t = self#emit_assert_term t
let assert_term' (self : #t) t = ignore (assert_term self t : Tr.Entry_id.t)
