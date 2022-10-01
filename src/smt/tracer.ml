open Sidekick_core
module Tr = Sidekick_trace
module V = Ser_value

class type t =
  object
    inherit Term.Tracer.t
    method emit_assert_term : Term.t -> Tr.Entry_id.t
    method emit_assert_clause : Lit.t list -> Tr.Entry_id.t
  end

class concrete (sink : Tr.Sink.t) : t =
  object
    inherit Term.Tracer.concrete ~sink as emit_t

    method emit_assert_term t =
      let id_t = emit_t#emit_term t in
      let v = V.int id_t in
      let id = Tr.Sink.emit sink ~tag:"AssT" v in
      id

    method emit_assert_clause (c : Lit.t list) =
      (* get a list of pairs *)
      let l =
        List.map
          (fun lit ->
            let sign = Lit.sign lit in
            let id_t = emit_t#emit_term @@ Lit.term lit in
            V.(list [ bool sign; int id_t ]))
          c
        |> V.list
      in
      let id = Tr.Sink.emit sink ~tag:"AssC" l in
      id
  end

class dummy : t =
  object
    inherit Term.Tracer.dummy
    method emit_assert_term _ = Tr.Entry_id.dummy
    method emit_assert_clause _ = Tr.Entry_id.dummy
  end

let assert_term (self : #t) t = self#emit_assert_term t
let assert_term' (self : #t) t = ignore (assert_term self t : Tr.Entry_id.t)
let assert_clause (self : #t) c = self#emit_assert_clause c
let assert_clause' (self : #t) c = ignore (assert_clause self c : Tr.Entry_id.t)
let assert_clause_arr' (self : #t) c = assert_clause' self (Array.to_list c)
let dummy : #t = new dummy
let concrete ~sink = new concrete sink
