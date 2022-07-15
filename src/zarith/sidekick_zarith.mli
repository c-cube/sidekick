module Int : Sidekick_arith.INT_FULL with type t = Z.t

module Rational :
  Sidekick_arith.RATIONAL with type t = Q.t and type bigint = Z.t
