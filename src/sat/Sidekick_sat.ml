(** Main API *)

module Solver_intf = Solver_intf

module type S = Solver_intf.S
module type LIT = Solver_intf.LIT
module type PLUGIN_CDCL_T = Solver_intf.PLUGIN_CDCL_T
module type PLUGIN_SAT = Solver_intf.PLUGIN_SAT
module type PROOF_RULES = Solver_intf.PROOF_RULES

type lbool = Solver_intf.lbool = L_true | L_false | L_undefined

module type SAT_STATE = Solver_intf.SAT_STATE

type 'form sat_state = 'form Solver_intf.sat_state

type ('lit, 'proof) reason = ('lit, 'proof) Solver_intf.reason =
  | Consequence of (unit -> 'lit list * 'proof)
[@@unboxed]

module type ACTS = Solver_intf.ACTS

type ('lit, 'proof, 'proof_step) acts =
  ('lit, 'proof, 'proof_step) Solver_intf.acts

type negated = bool

(** Print {!lbool} values *)
let pp_lbool out = function
  | L_true -> Format.fprintf out "true"
  | L_false -> Format.fprintf out "false"
  | L_undefined -> Format.fprintf out "undefined"

exception No_proof = Solver_intf.No_proof
exception Resource_exhausted = Solver_intf.Resource_exhausted

module Solver = Solver
module Make_cdcl_t = Solver.Make_cdcl_t
module Make_pure_sat = Solver.Make_pure_sat

module Proof_dummy = Proof_dummy
(** Module for dummy proofs based on unit *)
