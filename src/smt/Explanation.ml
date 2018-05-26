
open Solver_types

type t = explanation =
  | E_reduction
  | E_lit of lit
  | E_lits of lit list
  | E_congruence of cc_node * cc_node
  | E_injectivity of cc_node * cc_node
  | E_reduce_eq of cc_node * cc_node
  | E_custom of {
      name : ID.t; args : explanation list;
      pp : (ID.t * explanation list) Fmt.printer;
    }

let compare = cmp_exp
let equal a b = cmp_exp a b = 0

let pp = pp_explanation

let[@inline] lit l : t = E_lit l

module Set = CCSet.Make(struct
    type t = explanation
    let compare = compare
  end)

