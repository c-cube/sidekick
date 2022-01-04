
(** A reference to a previously defined object in the proof *)
type id = int

(** Representation of types *)
module Ty = struct
  type t =
    | Bool
    | Arrow of t array * t
    | App of string * t array
    | Ref of string

  let equal : t -> t -> bool = (=)
  let hash : t -> int = CCHash.poly
  let[@inline] view (self:t) : t = self

  let rec pp out (self:t) =
    match self with
    | Bool -> Fmt.string out "Bool"
    | Arrow (args, ret) ->
      Fmt.fprintf out "(@[->@ %a@ %a@])" (Util.pp_array pp) args pp ret
    | App (c, [||]) -> Fmt.string out c
    | App (c, args) ->
      Fmt.fprintf out "(@[%s@ %a@])" c (Util.pp_array pp) args
    | Ref name -> Fmt.fprintf out "(@@ %s)" name
end

module Fun = struct
  type t = string
  let pp out (self:t) = Fmt.string out self
  let equal : t -> t -> bool = (=)
  let hash : t -> int = CCHash.poly
end

module Cstor = Fun

(** Representation of terms, with explicit sharing *)
module T = struct
  type t =
    | Bool of bool
    | App_fun of Fun.t * t array
    | App_ho of t * t
    | Is_a of Fun.t * t
    | Ite of t * t * t
    | Not of t
    | Eq of t * t
    | Ref of string
  let[@inline] view (self:t) : t = self

  let equal : t -> t -> bool = (=)
  let hash : t -> int = CCHash.poly

  let true_ : t = Bool true
  let false_ : t = Bool false
  let bool b = Bool b
  let not_ = function Not x -> x | x -> Not x
  let eq a b : t = Eq (a,b)
  let ref name : t = Ref name
  let app_fun f args : t = App_fun (f, args)
  let const c = app_fun c [||]
  let app_ho a b : t = App_ho (a,b)
  let ite a b c : t = Ite (a,b,c)
  let is_a f t : t = Is_a (f,t)

  let rec pp out = function
    | Bool b -> Fmt.bool out b
    | Ite (a,b,c) -> Fmt.fprintf out "(@[if@ %a@ %a@ %a@])" pp a pp b pp c
    | App_fun (f,[||]) -> Fmt.string out f
    | App_fun (f,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_array pp) args
    | App_ho (f,a) -> Fmt.fprintf out "(@[%a@ %a@])" pp f pp a
    | Not a -> Fmt.fprintf out "(@[not@ %a@])" pp a
    | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
    | Ref name -> Fmt.fprintf out "(@@ %s)" name
    | Is_a (c,t) -> Fmt.fprintf out "(@[(_ is %a)@ %a@])" Fun.pp c pp t
end

type term = T.t
type ty = Ty.t

module Lit = struct
  type t =
    | L_eq of term * term
    | L_a of bool * term

  let pp_with ~pp_t out =
    function
    | L_eq (t,u) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp_t t pp_t u
    | L_a (false,t) -> Fmt.fprintf out "(@[not@ %a@])" pp_t t
    | L_a (true,t) -> pp_t out t

  let pp = pp_with ~pp_t:T.pp

  let eq t u = L_eq (t,u)
  let mk b t = L_a (b,t)
end

type clause = Lit.t list

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
  | Res of term * t * t
  | Res1 of t * t
  | Paramod1 of t * t
  | Rup of clause * t list
  | Clause_rw of {
      res: clause;
      c0: t;
      using: t list; (** the rewriting equations/atoms *)
    }
  | DT_isa_split of ty * term list
  | DT_isa_disj of ty * term * term
  | DT_cstor_inj of Cstor.t * int * term list * term list (* [c t…=c u… |- t_i=u_i] *)
  | Bool_true_is_true
  | Bool_true_neq_false
  | Bool_eq of term * term (* equal by pure boolean reasoning *)
  | Bool_c of bool_c_name * term list (* boolean tautology *)
  | Ite_true of term (* given [if a b c] returns [a=T |- if a b c=b] *)
  | Ite_false of term
  | LRA of clause
  | Composite of {
      (* some named (atomic) assumptions *)
      assumptions: (string * Lit.t) list;
      steps: composite_step array; (* last proof_rule is the proof *)
    }

and bool_c_name = string

and composite_step =
  | S_step_c of {
      name: string; (* name *)
      res: clause; (* result of [proof] *)
      proof: t; (* sub-proof *)
    }
  (** A named step in {!Composite}, with the expected result.
      This decouples the checking of the sub-proof, from its use in the rest
      of the proof, as we can use [res] even if checking [proof] failed. *)

  | S_step_anon of {
      name: string; (* name of step *)
      proof: t; (* proof *)
    }
    (** A named intermediate proof, to be reused in subsequent proofs.
        Unlike {!S_step_c} we do not specify the expected result
        so if this fails, any proof downstream will also fail. *)

  | S_define_t of term * term (* [const := t] *)
  | S_define_t_name of string * term (* [const := t] *)

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
let step_anon ~name proof : composite_step = S_step_anon {name;proof}
let deft c rhs : composite_step = S_define_t (c,rhs)
let deft_name c rhs : composite_step = S_define_t_name (c,rhs)

let is_trivial_refl = function
  | Refl _ -> true
  | _ -> false

let default=Unspecified
let sorry_c c = Sorry_c (Iter.to_rev_list c)
let sorry_c_l c = Sorry_c c
let sorry = Sorry
let refl t : t = Refl t
let ref_by_name name : t = Named name
let cc_lemma c : t = CC_lemma c
let cc_imply_l l t u : t =
  let l = List.filter (fun p -> not (is_trivial_refl p)) l in
  match l with
  | [] -> refl t (* only possible way [t=u] *)
  | l -> CC_lemma_imply (l, t, u)
let cc_imply2 h1 h2 t u : t = CC_lemma_imply ([h1; h2], t, u)
let assertion t = Assertion t
let assertion_c c = Assertion_c (Iter.to_rev_list c)
let assertion_c_l c = Assertion_c c
let rup c hyps : t = Rup (c,hyps)
let clause_rw c0 ~res ~using : t = Clause_rw{res;c0;using}
let composite_a ?(assms=[]) steps : t =
  Composite {assumptions=assms; steps}
let composite_l ?(assms=[]) steps : t =
  Composite {assumptions=assms; steps=Array.of_list steps}
let composite_iter ?(assms=[]) steps : t =
  let steps = Iter.to_array steps in
  Composite {assumptions=assms; steps}

let isa_split ty i = DT_isa_split (ty, Iter.to_rev_list i)
let isa_disj ty t u = DT_isa_disj (ty, t, u)
let cstor_inj c i t u = DT_cstor_inj (c, i, t, u)

let ite_true t = Ite_true t
let ite_false t = Ite_false t
let true_is_true : t = Bool_true_is_true
let true_neq_false : t = Bool_true_neq_false
let bool_eq a b : t = Bool_eq (a,b)
let bool_c name c : t = Bool_c (name, c)

let hres_l p l : t =
  let l = List.filter (function (P1 (Refl _)) -> false | _ -> true) l in
  if l=[] then p else Hres (p,l)
let hres_iter c i : t = hres_l c (Iter.to_list i)
let res ~pivot p1 p2 : t = Res (pivot,p1,p2)
let res1 p1 p2 : t = Res1 (p1,p2)
let paramod1 p1 p2 : t = Paramod1(p1,p2)

let lra_l c : t = LRA c
let lra c = LRA (Iter.to_rev_list c)
