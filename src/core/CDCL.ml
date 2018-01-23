
(** Main API *)

module Theory_intf = Theory_intf
module Solver_types_intf = Solver_types_intf
module Config = Config

module Res = Res

module type S = Solver_intf.S

type negated = Theory_intf.negated =
  | Negated
  | Same_sign

type ('formula, 'proof) res = ('formula, 'proof) Theory_intf.res =
  | Sat
  (** The current set of assumptions is satisfiable. *)
  | Unsat of 'formula list * 'proof
  (** The current set of assumptions is *NOT* satisfiable, and here is a
      theory tautology (with its proof), for which every litteral is false
      under the current assumptions. *)
(** Type returned by the theory. Formulas in the unsat clause must come from the
    current set of assumptions, i.e must have been encountered in a slice. *)

type 'form sat_state = 'form Solver_intf.sat_state = Sat_state of {
  eval : 'form -> bool;
  eval_level : 'form -> bool * int;
  iter_trail : ('form -> unit) -> unit;
}

type ('clause, 'proof) unsat_state = ('clause, 'proof) Solver_intf.unsat_state = Unsat_state of {
  unsat_conflict : unit -> 'clause;
  get_proof : unit -> 'proof;
}

type 'clause export = 'clause Solver_intf.export = {
  hyps : 'clause Vec.t;
  history : 'clause Vec.t;
  local : 'clause Vec.t;
}

type ('form, 'proof) actions = ('form,'proof) Theory_intf.actions = Actions of {
  push : 'form list -> 'proof -> unit;
  on_backtrack: (unit -> unit) -> unit;
  at_level_0 : unit -> bool;
}

type ('form, 'proof) slice_actions = ('form, 'proof) Theory_intf.slice_actions = Slice_acts of {
  slice_iter : ('form -> unit) -> unit;
  slice_propagate : 'form -> 'form list -> 'proof -> unit;
}

module Make(E : Theory_intf.S) = Solver.Make(Solver_types.Make(E))(E)

(**/**)
module Vec = Vec
module Log = Log
(**/**)
