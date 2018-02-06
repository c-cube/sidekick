
open Solver_types

type t = explanation

let compare = cmp_exp
let equal a b = cmp_exp a b = 0

let pp = pp_explanation

module Set = CCSet.Make(struct
    type t = explanation
    let compare = compare
  end)

