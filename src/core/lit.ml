open Sidekick_core_logic
module T = Term

type term = T.t
type t = { lit_term: term; lit_sign: bool }

let[@inline] neg l = { l with lit_sign = not l.lit_sign }
let[@inline] sign t = t.lit_sign
let[@inline] abs t = { t with lit_sign = true }
let[@inline] term (t : t) : term = t.lit_term
let[@inline] signed_term t = term t, sign t
let make ~sign t = { lit_sign = sign; lit_term = t }

let atom ?(sign = true) (t : term) : t =
  let sign', t = T_builtins.abs t in
  let sign =
    if not sign' then
      not sign
    else
      sign
  in
  make ~sign t

let make_eq ?sign store t u : t =
  let p = T_builtins.eq store t u in
  atom ?sign p

let equal a b = a.lit_sign = b.lit_sign && T.equal a.lit_term b.lit_term

let hash a =
  let sign = a.lit_sign in
  CCHash.combine3 2 (CCHash.bool sign) (T.hash a.lit_term)

let pp out l =
  if l.lit_sign then
    T.pp_debug out l.lit_term
  else
    Format.fprintf out "(@[@<1>¬@ %a@])" T.pp_debug l.lit_term

let norm_sign l =
  if l.lit_sign then
    l, true
  else
    neg l, false
