
open Solver_types

type t = lit = {
  lit_term: term;
  lit_sign : bool
}

let[@inline] neg l = {l with lit_sign=not l.lit_sign}
let[@inline] sign t = t.lit_sign
let[@inline] term (t:t): term = t.lit_term

let[@inline] abs t: t = {t with lit_sign=true}

let make ~sign t = {lit_sign=sign; lit_term=t}

let atom tst ?(sign=true) (t:term) : t =
  let t, sign' = Term.abs tst t in
  let sign = if not sign' then not sign else sign in
  make ~sign t

let[@inline] as_atom (lit:t) = lit.lit_term, lit.lit_sign

let hash = hash_lit
let compare = cmp_lit
let[@inline] equal a b = compare a b = 0
let pp = pp_lit
let print = pp

let norm l =
  if l.lit_sign then l, Msat.Solver_intf.Same_sign else neg l, Msat.Solver_intf.Negated

module Set = CCSet.Make(struct type t = lit let compare=compare end)
module Tbl = CCHashtbl.Make(struct type t = lit let equal=equal let hash=hash end)
