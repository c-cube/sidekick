(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(* Log&Module Init *)
(* ************************************************************************ *)

module Id = Dolmen.Id
module Ast = Dolmen.Term
module H = Hashtbl.Make(Id)
module Formula = Msat_tseitin.Make(Msat_sat.Th)

(* Exceptions *)
(* ************************************************************************ *)

exception Typing_error of string * Dolmen.Term.t

(* Identifiers *)
(* ************************************************************************ *)

type t = {
  symbols: Formula.atom H.t;
  fresh: Formula.fresh_state;
  st: Formula.state;
}

let create th : t = {
  symbols = H.create 42;
  fresh=th;
  st=Formula.create th;
}

let find_id st id =
  try
    H.find st.symbols id
  with Not_found ->
    let res = Msat_sat.Th.fresh st.fresh in
    H.add st.symbols id res;
    res

(* Actual parsing *)
(* ************************************************************************ *)

[@@@ocaml.warning "-9"]

let rec parse st = function
  | { Ast.term = Ast.Builtin Ast.True } ->
    Formula.f_true
  | { Ast.term = Ast.Builtin Ast.False } ->
    Formula.f_false
  | { Ast.term = Ast.Symbol id } ->
    let s = find_id st id in
    Formula.make_atom s
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Not }, [p]) }
  | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "not" } }, [p]) } ->
    Formula.make_not (parse st p)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.And }, l) }
  | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "and" } }, l) } ->
    Formula.make_and (List.map (parse st) l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Or }, l) }
  | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "or" } }, l) } ->
    Formula.make_or (List.map (parse st) l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Imply }, [p; q]) } ->
    Formula.make_imply (parse st p) (parse st q)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Equiv }, [p; q]) } ->
    Formula.make_equiv (parse st p) (parse st q)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Xor }, [p; q]) } ->
    Formula.make_xor (parse st p) (parse st q)
  | t ->
    raise (Typing_error ("Term is not a pure proposition", t))

[@@@ocaml.warning "+9"]

(* Exported functions *)
(* ************************************************************************ *)

let decl _ _ t =
  raise (Typing_error ("Declarations are not allowed in pure sat", t))

let def _ _ t =
  raise (Typing_error ("Definitions are not allowed in pure sat", t))

let assumptions st t =
  let f = parse st t in
  let cnf = Formula.make_cnf st.st f in
  List.map (function
      | [ x ] -> x
      | _ -> assert false
    ) cnf

let antecedent st t =
  let f = parse st t in
  Formula.make_cnf st.st f

let consequent st t =
  let f = parse st t in
  Formula.make_cnf st.st @@ Formula.make_not f

