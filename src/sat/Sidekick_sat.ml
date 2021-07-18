(** Main API *)


module Solver_intf = Solver_intf

module type S = Solver_intf.S
module type FORMULA = Solver_intf.FORMULA
module type PLUGIN_CDCL_T = Solver_intf.PLUGIN_CDCL_T
module type PROOF = Solver_intf.PROOF

type lbool = Solver_intf.lbool = L_true | L_false | L_undefined

type 'form sat_state = 'form Solver_intf.sat_state = {
  eval : 'form -> bool;
  eval_level : 'form -> bool * int;
  iter_trail : ('form -> unit) -> unit;
}

type ('atom,'clause, 'proof) unsat_state = ('atom,'clause, 'proof) Solver_intf.unsat_state = {
  unsat_conflict : unit -> 'clause;
  get_proof : unit -> 'proof;
  unsat_assumptions: unit -> 'atom list;
}
type 'clause export = 'clause Solver_intf.export = {
  hyps : 'clause Vec.t;
  history : 'clause Vec.t;
}

type ('formula, 'proof) reason = ('formula, 'proof) Solver_intf.reason =
  | Consequence of (unit -> 'formula list * 'proof)

type ('formula, 'proof) acts = ('formula, 'proof) Solver_intf.acts = {
  acts_iter_assumptions: ('formula -> unit) -> unit;
  acts_eval_lit: 'formula -> lbool;
  acts_mk_lit: ?default_pol:bool -> 'formula -> unit;
  acts_add_clause : ?keep:bool -> 'formula list -> 'proof -> unit;
  acts_raise_conflict: 'b. 'formula list -> 'proof -> 'b;
  acts_propagate : 'formula -> ('formula, 'proof) reason -> unit;
  acts_add_decision_lit: 'formula -> bool -> unit;
}

type negated = Solver_intf.negated = Negated | Same_sign

(** Print {!negated} values *)
let pp_negated out = function
  | Negated -> Format.fprintf out "negated"
  | Same_sign -> Format.fprintf out "same-sign"

(** Print {!lbool} values *)
let pp_lbool out = function
  | L_true -> Format.fprintf out "true"
  | L_false -> Format.fprintf out "false"
  | L_undefined -> Format.fprintf out "undefined"

exception No_proof = Solver_intf.No_proof

module Make_cdcl_t = Solver.Make_cdcl_t
