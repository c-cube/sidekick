open Sidekick_core
module Tr = Sidekick_trace
module V = Ser_value

class type t =
  object
    inherit Term.Tracer.t
    method emit_assert_term : Term.t -> Tr.Entry_id.t
    inherit Clause_tracer.t
    method emit_assert_term : Term.t -> Tr.Entry_id.t
  end

class concrete (sink : Tr.Sink.t) : t =
  object (self)
    inherit Term.Tracer.concrete ~sink as emit_t

    method emit_assert_term t =
      let id_t = emit_t#emit_term t in
      let v = V.int id_t in
      let id = Tr.Sink.emit sink ~tag:"AssT" v in
      id

    method encode_lit (lit : Lit.t) : V.t =
      let sign = Lit.sign lit in
      let id_t = emit_t#emit_term @@ Lit.term lit in
      V.(list [ bool sign; int id_t ])

    method assert_clause ~id (c : Lit.t Iter.t) =
      (* get a list of pairs *)
      let l = Iter.map self#encode_lit c |> Iter.to_rev_list |> V.list in
      let v = V.(dict_of_list [ "id", int id; "c", l ]) in
      let id = Tr.Sink.emit sink ~tag:"AssC" v in
      id

    method unsat_clause ~id =
      let v = Ser_value.(dict_of_list [ "id", int id ]) in
      Tr.Sink.emit sink ~tag:"UnsatC" v

    method delete_clause ~id _lits : unit =
      let v = Ser_value.(dict_of_list [ "id", int id ]) in
      ignore (Tr.Sink.emit sink ~tag:"DelCSat" v : Tr.Entry_id.t)
  end

class dummy : t =
  object
    inherit Term.Tracer.dummy
    inherit Clause_tracer.dummy
    method emit_assert_term _ = Tr.Entry_id.dummy
  end

let dummy : #t = new dummy
let make ~sink () = new concrete sink
let assert_clause (self : #t) ~id c : Tr.Entry_id.t = self#assert_clause ~id c

let assert_clause' (self : #t) ~id c : unit =
  ignore (self#assert_clause ~id c : Tr.Entry_id.t)

let unsat_clause (self : #t) ~id : Tr.Entry_id.t = self#unsat_clause ~id

let unsat_clause' (self : #t) ~id : unit =
  ignore (self#unsat_clause ~id : Tr.Entry_id.t)

let delete_clause (self : #t) ~id c = self#delete_clause ~id c
let encode_lit (self : #t) lit = self#encode_lit lit
let assert_term (self : #t) t = self#emit_assert_term t
let assert_term' (self : #t) t = ignore (assert_term self t : Tr.Entry_id.t)
