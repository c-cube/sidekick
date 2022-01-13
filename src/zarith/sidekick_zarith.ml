

module Int : Sidekick_arith.INT with type t = Z.t = struct
  include Z
  include Z.Compare
  let pp = pp_print
end

module Rational
  : Sidekick_arith.RATIONAL with type t = Q.t and type bigint = Z.t
= struct
  type bigint = Z.t
  include Q
  let denum = den
  let pp = pp_print
  let hash a = Hashtbl.hash (Z.hash (num a), Z.hash (den a))

  let infinity = Q.inf
  let minus_infinity = Q.minus_inf
  let is_real = Q.is_real
  let is_int q = is_real q && Z.(equal (denum q) one)
  let as_int q = if is_int q then Some (to_bigint q) else None
  let floor q = Q.to_bigint q
  let ceil q =
    let n = Q.to_bigint q in
    if is_int q then n else Z.(n + one)

  let pp_approx n out q = Format.fprintf out "%*.1f" n (Q.to_float q)
end

