
module T = Sidekick_base_term.Term
type term = T.t

type t =
  | Unspecified
  | Sorry of term
  | CC_lemma_imply of t list * term * term
  | CC_lemma of (term * bool) list
  | Assertion of term

let default=Unspecified
let sorry t = Sorry t
let make_cc iter : t = CC_lemma (Iter.to_rev_list iter)
let assertion t = Assertion t



let rec pp out (self:t) : unit =
  let pp_signed_t_ out (t,b) =
    if b then T.pp out t else Fmt.fprintf out "(@[not@ %a@])" T.pp t
  in
  match self with
  | Unspecified -> Fmt.string out "<unspecified>"
  | CC_lemma_imply (l,t,u) ->
    Fmt.fprintf out "(@[cc-lemma@ (@[%a@])@])"
  | CC_lemma l ->
    Fmt.fprintf out "(@[cc-lemma@ (@[%a@])@])"
      Fmt.(list ~sep:(return "@ ") pp_lit) l
