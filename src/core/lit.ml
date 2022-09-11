open Sidekick_core_logic
module T = Term

type term = T.t
type t = { lit_term: term; lit_sign: bool }

let[@inline] neg l = { l with lit_sign = not l.lit_sign }
let[@inline] sign l = l.lit_sign
let[@inline] abs l = { l with lit_sign = true }
let[@inline] term (l : t) : term = l.lit_term
let[@inline] signed_term l = term l, sign l
let[@inline] make_ ~sign t : t = { lit_sign = sign; lit_term = t }

let atom ?(sign = true) tst (t : term) : t =
  let sign', t = T_builtins.abs tst t in
  assert (T_builtins.is_bool (Term.ty t));
  let sign = sign = sign' in
  make_ ~sign t

let make_eq ?sign store t u : t =
  let p = T_builtins.eq store t u in
  atom ?sign store p

let equal a b = a.lit_sign = b.lit_sign && T.equal a.lit_term b.lit_term

let compare a b =
  if a.lit_sign = b.lit_sign then
    T.compare a.lit_term b.lit_term
  else
    CCOrd.bool a.lit_sign b.lit_sign

let hash a =
  let sign = a.lit_sign in
  CCHash.combine3 2 (CCHash.bool sign) (T.hash a.lit_term)

let pp out l =
  if l.lit_sign then
    T_printer.pp out l.lit_term
  else
    Format.fprintf out "(@[@<1>¬@ %a@])" T_printer.pp l.lit_term

let norm_sign l =
  if l.lit_sign then
    l, true
  else
    neg l, false

module As_key = struct
  type nonrec t = t

  let equal = equal
  let hash = hash
  let compare = compare
end

module Map = CCMap.Make (As_key)
module Set = CCSet.Make (As_key)
module Tbl = CCHashtbl.Make (As_key)
