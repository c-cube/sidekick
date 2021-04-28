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

let lit_not = function
  | L_eq (a,b) -> L_neq(a,b)
  | L_neq (a,b) -> L_eq(a,b)
  | L_a t -> L_na t
  | L_na t -> L_a t

let pp_lit_with ~pp_t out = function
  | L_eq (t,u) -> Fmt.fprintf out "(@[+@ (@[=@ %a@ %a@])@])" pp_t t pp_t u
  | L_neq (t,u) -> Fmt.fprintf out "(@[-@ (@[=@ %a@ %a@])@])" pp_t t pp_t u
  | L_a t -> Fmt.fprintf out "(@[+@ %a@])" pp_t t
  | L_na t -> Fmt.fprintf out "(@[-@ %a@])" pp_t t
let pp_lit = pp_lit_with ~pp_t:Term.pp

let lit_a t = L_a t
let lit_na t = L_na t
let lit_eq t u = L_eq (t,u)
let lit_neq t u = L_neq (t,u)
let lit_st (t,b) = if b then lit_a t else lit_na t

type clause = lit list

type t =
  | Unspecified
  | Sorry (* NOTE: v. bad as we don't even specify the return *)
  | Sorry_c of clause
  | Named of string (* refers to previously defined clause *)
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
  | Bool_c of clause (* boolean tautology *)
  | Ite_true of term (* given [if a b c] returns [a=T |- if a b c=b] *)
  | Ite_false of term
  | With_def of term list * t (* [with_def ts p] is [p] using definitions of [ts] *)
  | LRA of clause
  | Composite of {
      (* some named (atomic) assumptions *)
      assumptions: (string * lit) list;
      steps: composite_step list; (* last step is the proof *)
    }

and composite_step =
  | S_step_c of {
      name: string; (* name *)
      res: clause; (* result of [proof] *)
      proof: t; (* sub-proof *)
    }
  | S_define_t of term * term (* [const := t] *)

  (* TODO: step to name a term (not define it), to keep sharing?
     or do we do that when we print/serialize the proof *)

and hres_step =
  | R of { pivot: term; p: t}
  | R1 of t
  | P of { lhs: term; rhs: term; p: t}
  | P1 of t

let r p ~pivot : hres_step = R { pivot; p }
let r1 p = R1 p
let p p ~lhs ~rhs : hres_step = P { p; lhs; rhs }
let p1 p = P1 p

let stepc ~name res proof : composite_step = S_step_c {proof;name;res}
let deft c rhs : composite_step = S_define_t (c,rhs)

let is_trivial_refl = function
  | Refl _ -> true
  | _ -> false

let default=Unspecified
let sorry_c c = Sorry_c (Iter.to_rev_list c)
let sorry_c_l c = Sorry_c c
let sorry = Sorry
let refl t : t = Refl t
let ref_by_name name : t = Named name
let make_cc iter : t = CC_lemma (Iter.to_rev_list iter)
let cc_lemma c : t = CC_lemma (Iter.to_rev_list c)
let cc_imply_l l t u : t = CC_lemma_imply (l, t, u)
let cc_imply2 h1 h2 t u : t = CC_lemma_imply ([h1; h2], t, u)
let assertion t = Assertion t
let assertion_c c = Assertion_c (Iter.to_rev_list c)
let assertion_c_l c = Assertion_c c
let with_defs ts p = match ts with [] -> p | _ -> With_def (ts, p)
let composite_l ?(assms=[]) steps : t =
  Composite {assumptions=assms; steps}
let composite_iter ?(assms=[]) steps : t =
  let steps = Iter.to_list steps in
  Composite {assumptions=assms; steps}

let isa_split ty i = DT_isa_split (ty, Iter.to_rev_list i)
let isa_disj ty t u = DT_isa_disj (ty, t, u)
let cstor_inj c i t u = DT_cstor_inj (c, i, t, u)

let ite_true t = Ite_true t
let ite_false t = Ite_false t
let true_is_true : t = Bool_true_is_true
let true_neq_false : t = Bool_true_neq_false
let bool_eq a b : t = Bool_eq (a,b)
let bool_c c : t = Bool_c c

let hres_l c l : t = Hres (c,l)
let hres_iter c i : t = Hres (c, Iter.to_list i)

let lra_l c : t = LRA c
let lra c = LRA (Iter.to_rev_list c)

module Quip = struct
  (*
  TODO: make sure we print terms properly
  TODO: define/use [deft] for printing shared terms
  *)

  let pp_l ppx out l = Fmt.(list ~sep:(return "@ ") ppx) out l
  let pp_cl out c = Fmt.fprintf out "(@[cl@ %a@])" (pp_l pp_lit) c

  let rec pp_rec out (self:t) : unit =
    match self with
    | Unspecified -> Fmt.string out "<unspecified>"
    | Named s -> Fmt.fprintf out "(ref %s)" s
    | CC_lemma l ->
      Fmt.fprintf out "(@[cc-lemma@ %a@])" pp_cl l
    | CC_lemma_imply (l,t,u) ->
      Fmt.fprintf out "(@[cc-lemma-imply@ (@[%a@])@ (@[=@ %a@ %a@])@])"
        (pp_l pp_rec) l T.pp t T.pp u
    | Refl t -> Fmt.fprintf out "(@[refl@ %a@])" T.pp t
    | Sorry -> Fmt.string out "sorry"
    | Sorry_c c -> Fmt.fprintf out "(@[sorry-c@ %a@])" pp_cl c
    | Bool_true_is_true -> Fmt.string out "true-is-true"
    | Bool_true_neq_false -> Fmt.string out "(@[!= T F@])"
    | Bool_eq (a,b) -> Fmt.fprintf out "(@[bool-eq@ %a@ %a@])" T.pp a T.pp b
    | Bool_c c -> Fmt.fprintf out "(@[bool-c@ %a@])" pp_cl c
    | Assertion t -> Fmt.fprintf out "(@[assert@ %a@])" T.pp t
    | Assertion_c c ->
      Fmt.fprintf out "(@[assert-c@ %a@])" pp_cl c
    | Hres (c, l) ->
      Fmt.fprintf out "(@[hres@ (@[init@ %a@])@ %a@])" pp_rec c
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
    | With_def (ts,p) ->
      Fmt.fprintf out "(@[with-defs (@[%a@])@ %a@])" (pp_l T.pp) ts pp_rec p
    | LRA c -> Fmt.fprintf out "(@[lra@ %a@])" pp_cl c
    | Composite {steps; assumptions} ->
      let pp_ass out (n,a) = Fmt.fprintf out "(@[assuming@ (name %s) %a@])" n pp_lit a in
      Fmt.fprintf out "(@[steps@ (@[%a@])@ (@[%a@])@])"
        (pp_l pp_ass) assumptions (pp_l pp_composite_step) steps

  and pp_composite_step out = function
    | S_define_c {name;res;proof} ->
      Fmt.fprintf out "(@[defc %s@ %a@ %a@])" name pp_cl res pp_rec proof
    | S_define_t (c,rhs) ->
      Fmt.fprintf out "(@[deft@ %a@ %a@])" Term.pp c Term.pp rhs

  (*
    | S_define_t (name, t) ->
      Fmt.fprintf out "(@[deft %s %a@])" name Term.pp t
  *)

  and pp_hres_step out = function
    | R {pivot; p} ->
      Fmt.fprintf out "(@[r@ (@[pivot@ %a@])@ %a@])" T.pp pivot pp_rec p
    | R1 p -> Fmt.fprintf out "(@[r1@ %a@])"  pp_rec p
    | P {p; lhs; rhs} ->
      Fmt.fprintf out "(@[r@ (@[lhs@ %a@])@ (@[rhs@ %a@])@ %a@])"
        T.pp lhs T.pp rhs pp_rec p
    | P1 p -> Fmt.fprintf out "(@[p1@ %a@])"  pp_rec p

  (* toplevel wrapper *)
  let pp out self =
    Fmt.fprintf out "(@[quip 1@ %a@])" pp_rec self
end

let pp_debug = Quip.pp_rec
