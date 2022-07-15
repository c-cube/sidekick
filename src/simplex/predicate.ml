type t = Leq | Geq | Lt | Gt | Eq | Neq

let neg = function
  | Leq -> Gt
  | Lt -> Geq
  | Eq -> Neq
  | Neq -> Eq
  | Geq -> Lt
  | Gt -> Leq

let neg_sign = function
  | Leq -> Geq
  | Lt -> Gt
  | Geq -> Leq
  | Gt -> Lt
  | Neq -> Neq
  | Eq -> Eq

let to_string = function
  | Leq -> "=<"
  | Geq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Eq -> "="
  | Neq -> "!="

let pp out (self : t) = Fmt.string out (to_string self)
