
open Solver_types

type t = explanation =
  | E_reduction (* by pure reduction, tautologically equal *)
  | E_merges of (cc_node * cc_node) list (* caused by these merges *)
  | E_lit of lit (* because of this literal *)
  | E_lits of lit list (* because of this (true) conjunction *)
  | E_congruence of cc_node * cc_node (* these terms are congruent *)

let compare = cmp_exp
let equal a b = cmp_exp a b = 0

let pp = pp_explanation

let mk_merges l : t = E_merges l
let mk_lit l : t = E_lit l
let mk_lits = function [x] -> mk_lit x | l -> E_lits l
let mk_reduction : t = E_reduction
let mk_congruence t u = E_congruence (t,u)

let[@inline] lit l : t = E_lit l

module Set = CCSet.Make(struct
    type t = explanation
    let compare = compare
  end)

