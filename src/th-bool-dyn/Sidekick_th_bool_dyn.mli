(** Theory of boolean formulas.

    This handles formulas containing "and", "or", "=>", "if-then-else", etc.

    The difference with {!Sidekick_th_bool_static} is that here, clausification
    of a formula [F] is done only when [F] is on the trail.
*)

module Intf = Intf
module Proof_rules = Proof_rules
open Intf

module type ARG = Intf.ARG

val theory : (module ARG) -> SMT.Theory.t
