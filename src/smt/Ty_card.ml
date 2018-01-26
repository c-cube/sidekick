
open Solver_types

type t = ty_card

let (+) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
let ( * ) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
let ( ^ ) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
let finite = Finite
let infinite = Infinite

let sum = List.fold_left (+) Finite
let product = List.fold_left ( * ) Finite

let equal = (=)
let compare = Pervasives.compare
let pp out = function
  | Finite -> Fmt.string out "finite"
  | Infinite -> Fmt.string out "infinite"
