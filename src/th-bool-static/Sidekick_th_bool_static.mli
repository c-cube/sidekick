(** Theory of boolean formulas.

    This handles formulas containing "and", "or", "=>", "if-then-else", etc.
*)

module Intf = Intf
module Proof_rules = Proof_rules
open Intf

module type ARG = Intf.ARG

val theory : (module ARG) -> SMT.Theory.t
