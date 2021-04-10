
module T = Sidekick_base_term.Term
type term = T.t

type t =
  | Unspecified
  | CC_lemma of (term * bool) list
let default=Unspecified
let make_cc iter : t = CC_lemma (Iter.to_rev_list iter)
let pp out = function
  | Unspecified -> Fmt.string out "<unspecified>"
  | CC_lemma l ->
    let pp_lit out (t,b) =
      if b then T.pp out t else Fmt.fprintf out "(@[not@ %a@])" T.pp t
    in
    Fmt.fprintf out "(@[cc-lemma@ (@[%a@])@])"
      Fmt.(list ~sep:(return "@ ") pp_lit) l
