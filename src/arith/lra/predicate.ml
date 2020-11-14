
type t = Leq | Geq | Lt | Gt | Eq | Neq

let neg = function
  | Leq -> Gt
  | Lt -> Geq
  | Eq -> Neq
  | Neq -> Eq
  | Geq -> Lt
  | Gt -> Leq

let to_string = function
  | Leq -> "=<" | Geq -> ">=" | Lt -> "<"
  | Gt -> ">" | Eq -> "=" | Neq -> "!="

let pp out (self:t) = Fmt.string out (to_string self)

