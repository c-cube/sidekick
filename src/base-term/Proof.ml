open Base_types

module T = Term
module Ty = Ty
type term = T.t
type ty = Ty.t

type lit =
  | L_eq of term * term
  | L_neq of term * term
  | L_a of term
  | L_na of term

let not = function
  | L_eq (a,b) -> L_neq(a,b)
  | L_neq (a,b) -> L_eq(a,b)
  | L_a t -> L_na t
  | L_na t -> L_a t

let pp_lit out = function
  | L_eq (t,u) -> Fmt.fprintf out "(@[+@ (@[=@ %a@ %a@])@])" T.pp t T.pp u
  | L_neq (t,u) -> Fmt.fprintf out "(@[-@ (@[=@ %a@ %a@])@])" T.pp t T.pp u
  | L_a t -> Fmt.fprintf out "(@[+@ %a@])" T.pp t
  | L_na t -> Fmt.fprintf out "(@[-@ %a@])" T.pp t

let a t = L_a t
let na t = L_na t
let eq t u = L_eq (t,u)
let neq t u = L_neq (t,u)
let lit_st (t,b) = if b then a t else na t

type clause = lit list

type t =
  | Unspecified
  | Sorry (* NOTE: v. bad as we don't even specify the return *)
  | Sorry_c of clause
  | Refl of term
  | CC_lemma_imply of t list * term * term
  | CC_lemma of clause
  | Assertion of term
  | Assertion_c of clause
  | Hres of t * hres_step list
  | DT_isa_split of ty * term list
  | DT_isa_disj of ty * term * term
  | DT_cstor_inj of Cstor.t * int * term list * term list (* [c t…=c u… |- t_i=u_i] *)
  | Bool_true_is_true
  | Bool_true_neq_false
  | Bool_eq of term * term (* equal by pure boolean reasoning *)
  | Ite_true of term (* given [if a b c] returns [a=T |- if a b c=b] *)
  | Ite_false of term
  | LRA of clause

and hres_step =
  | R of { pivot: term; p: t}
  | R1 of t
  | P of { lhs: term; rhs: term; p: t}
  | P1 of t

let r p ~pivot : hres_step = R { pivot; p }
let r1 p = R1 p
let p p ~lhs ~rhs : hres_step = P { p; lhs; rhs }
let p1 p = P1 p

let default=Unspecified
let sorry_c c = Sorry_c (Iter.to_rev_list c)
let sorry_c_l c = Sorry_c c
let sorry = Sorry
let refl t : t = Refl t
let make_cc iter : t = CC_lemma (Iter.to_rev_list iter)
let cc_lemma c : t = CC_lemma (Iter.to_rev_list c)
let cc_imply_l l t u : t = CC_lemma_imply (l, t, u)
let cc_imply2 h1 h2 t u : t = CC_lemma_imply ([h1; h2], t, u)
let assertion t = Assertion t
let assertion_c c = Assertion_c (Iter.to_rev_list c)
let assertion_c_l c = Assertion_c c

let isa_split ty i = DT_isa_split (ty, Iter.to_rev_list i)
let isa_disj ty t u = DT_isa_disj (ty, t, u)
let cstor_inj c i t u = DT_cstor_inj (c, i, t, u)

let ite_true t = Ite_true t
let ite_false t = Ite_false t
let true_is_true : t = Bool_true_is_true
let true_neq_false : t = Bool_true_neq_false
let bool_eq a b : t = Bool_eq (a,b)

let hres_l c l : t = Hres (c,l)
let hres_iter c i : t = Hres (c, Iter.to_list i)

let lra_l c : t = LRA c
let lra c = LRA (Iter.to_rev_list c)

let rec pp out (self:t) : unit =
  let pp_l ppx out l = Fmt.(list ~sep:(return "@ ") ppx) out l in
  let pp_cl out c = Fmt.fprintf out "(@[cl@ %a@])" (pp_l pp_lit) c in
  match self with
  | Unspecified -> Fmt.string out "<unspecified>"
  | CC_lemma l ->
    Fmt.fprintf out "(@[cc-lemma@ %a@])" pp_cl l
  | CC_lemma_imply (l,t,u) ->
    Fmt.fprintf out "(@[cc-lemma-imply@ (@[%a@])@ (@[=@ %a@ %a@])@])"
      (pp_l pp) l T.pp t T.pp u
  | Refl t -> Fmt.fprintf out "(@[refl@ %a@])" T.pp t
  | Sorry -> Fmt.string out "sorry"
  | Sorry_c c -> Fmt.fprintf out "(@[sorry-c@ %a@])" pp_cl c
  | Bool_true_is_true -> Fmt.string out "true-is-true"
  | Bool_true_neq_false -> Fmt.string out "(@[!= T F@])"
  | Bool_eq (a,b) -> Fmt.fprintf out "(@[bool-eq@ %a@ %a@])" T.pp a T.pp b
  | Assertion t -> Fmt.fprintf out "(@[assert@ %a@])" T.pp t
  | Assertion_c c ->
    Fmt.fprintf out "(@[assert-c@ %a@])" pp_cl c
  | Hres (c, l) ->
    Fmt.fprintf out "(@[hres@ (@[init@ %a@]) %a@])" pp c
      (pp_l pp_hres_step) l
  | DT_isa_split (ty,l) ->
    Fmt.fprintf out "(@[dt.isa.split@ (@[ty %a@])@ (@[cases@ %a@])@])"
      Ty.pp ty (pp_l T.pp) l
  | DT_isa_disj (ty,t,u) ->
    Fmt.fprintf out "(@[dt.isa.disj@ (@[ty %a@])@ %a@ %a@])" Ty.pp ty T.pp t T.pp u
  | DT_cstor_inj (c,i,ts,us) ->
    Fmt.fprintf out "(@[dt.cstor.inj %d@ (@[%a@ %a@])@ (@[%a@ %a@])@])"
      i Cstor.pp c (pp_l T.pp) ts Cstor.pp c (pp_l T.pp) us
  | Ite_true t -> Fmt.fprintf out "(@[ite-true@ %a@])" T.pp t
  | Ite_false t -> Fmt.fprintf out "(@[ite-false@ %a@])" T.pp t
  | LRA c -> Fmt.fprintf out "(@[lra@ %a@])" pp_cl c

and pp_hres_step out = function
  | R {pivot; p} ->
    Fmt.fprintf out "(@[r@ (@[pivot@ %a@])@ %a@])" T.pp pivot pp p
  | R1 p -> Fmt.fprintf out "(@[r1@ %a@])"  pp p
  | P {p; lhs; rhs} ->
    Fmt.fprintf out "(@[r@ (@[lhs@ %a@])@ (@[rhs@ %a@])@ %a@])"
      T.pp lhs T.pp rhs pp p
  | P1 p -> Fmt.fprintf out "(@[p1@ %a@])"  pp p
