module Tr = Sidekick_trace

class type t =
  object
    method assert_clause : id:int -> Lit.t Iter.t -> Tr.Entry_id.t
    method delete_clause : id:int -> Lit.t Iter.t -> unit
    method unsat_clause : id:int -> Tr.Entry_id.t
    method encode_lit : Lit.t -> Ser_value.t
  end

class dummy : t =
  object
    method assert_clause ~id:_ _ = Tr.Entry_id.dummy
    method delete_clause ~id:_ _ = ()
    method unsat_clause ~id:_ = Tr.Entry_id.dummy
    method encode_lit _ = Ser_value.null
  end

let dummy : t = new dummy
let assert_clause (self : #t) ~id c : Tr.Entry_id.t = self#assert_clause ~id c

let assert_clause' (self : #t) ~id c : unit =
  ignore (self#assert_clause ~id c : Tr.Entry_id.t)

let unsat_clause (self : #t) ~id : Tr.Entry_id.t = self#unsat_clause ~id

let unsat_clause' (self : #t) ~id : unit =
  ignore (self#unsat_clause ~id : Tr.Entry_id.t)

let delete_clause (self : #t) ~id c = self#delete_clause ~id c
let encode_lit (self : #t) lit = self#encode_lit lit
