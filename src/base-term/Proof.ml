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
  | Bool_c of bool_c_name * clause (* boolean tautology *)
  | Ite_true of term (* given [if a b c] returns [a=T |- if a b c=b] *)
  | Ite_false of term
  | LRA of clause
  | Composite of {
      (* some named (atomic) assumptions *)
      assumptions: (string * lit) list;
      steps: composite_step array; (* last step is the proof *)
    }

and bool_c_name = string

and composite_step =
  | S_step_c of {
      name: string; (* name *)
      res: clause; (* result of [proof] *)
      proof: t; (* sub-proof *)
    }
  | S_define_t of term * term (* [const := t] *)
  | S_define_t_name of string * term (* [const := t] *)

  (* TODO: be able to name clauses, to be expanded at parsing.
     note that this is not the same as [S_step_c] which defines an
     explicit step with a conclusion and proofs that can be exploited
     separately.

     We could introduce that in Compress.rename…

  | S_define_c of string * clause (* [name := c] *)
   *)

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
let make_cc iter : t = CC_lemma (Iter.to_rev_list iter)
let cc_lemma c : t = CC_lemma (Iter.to_rev_list c)
let cc_imply_l l t u : t =
  let l = List.filter (fun p -> not (is_trivial_refl p)) l in
  match l with
  | [] -> refl t (* only possible way [t=u] *)
  | l -> CC_lemma_imply (l, t, u)
let cc_imply2 h1 h2 t u : t = CC_lemma_imply ([h1; h2], t, u)
let assertion t = Assertion t
let assertion_c c = Assertion_c (Iter.to_rev_list c)
let assertion_c_l c = Assertion_c c
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

let hres_l c l : t = Hres (c,l)
let hres_iter c i : t = Hres (c, Iter.to_list i)

let lra_l c : t = LRA c
let lra c = LRA (Iter.to_rev_list c)

let iter_lit ~f_t = function
  | L_eq (a,b) | L_neq (a,b) -> f_t a; f_t b
  | L_a t | L_na t -> f_t t

let iter_p (p:t) ~f_t ~f_step ~f_clause ~f_p : unit =
  match p with
  | Unspecified | Sorry -> ()
  | Sorry_c c -> f_clause c
  | Named _ -> ()
  | Refl t -> f_t t
  | CC_lemma_imply (ps, t, u) -> List.iter f_p ps; f_t t; f_t u
  | CC_lemma c | Assertion_c c -> f_clause c
  | Assertion t -> f_t t
  | Hres (i, l) ->
    f_p i;
    List.iter
      (function
        | R1 p -> f_p p
        | P1 p -> f_p p
        | R {pivot;p} -> f_p p; f_t pivot
        | P {lhs;rhs;p} -> f_p p; f_t lhs; f_t rhs)
      l
  | DT_isa_split (_, l) -> List.iter f_t l
  | DT_isa_disj (_, t, u) -> f_t t; f_t u
  | DT_cstor_inj (_, _c, ts, us) -> List.iter f_t ts; List.iter f_t us
  | Bool_true_is_true | Bool_true_neq_false -> ()
  | Bool_eq (t, u) -> f_t t; f_t u
  | Bool_c (_,c) -> f_clause c
  | Ite_true t | Ite_false t -> f_t t
  | LRA c -> f_clause c
  | Composite { assumptions; steps } ->
    List.iter (fun (_,lit) -> iter_lit ~f_t lit) assumptions;
    Array.iter f_step steps;

(** {2 Compress by making more sharing explicit} *)
module Compress = struct
  type 'a shared_status =
    | First (* first occurrence of t *)
    | Shared (* multiple occurrences observed *)
    | Named of 'a (* already named it *)

  (* is [t] too small to be shared? *)
  let rec is_small_ t =
    let open Term_cell in
    match T.view t with
    | Bool _ -> true
    | App_fun (_, a) -> IArray.is_empty a (* only constants are small *)
    | Not u -> is_small_ u
    | Eq (_, _) | Ite (_, _, _) -> false
    | LRA _ -> false

  type name = N_s of string | N_t of T.t
  type sharing_info = {
    terms: name shared_status T.Tbl.t; (* sharing for non-small terms *)
  }

  let no_sharing : sharing_info =
    { terms = T.Tbl.create 8 }

  (* traverse [p] and apply [f_t] to subterms (except to [c] in [c := rhs]) *)
  let rec traverse_proof_ ?on_step ~f_t (p:t) : unit =
    let recurse = traverse_proof_ ?on_step ~f_t in
    let f_step s =
      CCOpt.iter (fun f->f s) on_step;
      traverse_step_ ~f_t s
    in
    iter_p p
      ~f_t
      ~f_clause:(traverse_clause_ ~f_t)
      ~f_step
      ~f_p:recurse
  and traverse_step_ ~f_t = function
    | S_define_t_name (_, rhs)
    | S_define_t (_, rhs) -> f_t rhs
    | S_step_c {name=_; res; proof} ->
      traverse_clause_ ~f_t res; traverse_proof_ ~f_t proof
  and traverse_clause_ ~f_t c : unit =
    List.iter (iter_lit ~f_t) c

  (** [find_sharing p] returns a {!sharing_info} which contains sharing information.
      This information can be used during printing to reduce the
      number of duplicated sub-terms that are printed. *)
  let find_sharing p : sharing_info =
    let self = {terms=T.Tbl.create 32} in

    let traverse_t t =
      T.iter_dag t
        (fun u ->
           if not (is_small_ u) then (
             match T.Tbl.find_opt self.terms u with
             | None -> T.Tbl.add self.terms u First
             | Some First -> T.Tbl.replace self.terms u Shared
             | Some (Shared | Named _) -> ()
           ))
    in

    (* if a term is already name, remember that, do not rename it *)
    let on_step = function
      | S_define_t_name (n,rhs) ->
        T.Tbl.replace self.terms rhs (Named (N_s n));
      | S_define_t (c,rhs) ->
        T.Tbl.replace self.terms rhs (Named (N_t c));
      | S_step_c _ -> ()
    in

    traverse_proof_ p ~on_step ~f_t:traverse_t;
    self

  (** [renaming sharing p] returns a new proof [p'] with more definitions.
      It also modifies [sharing] so that the newly defined objects are
      mapped to {!Named}, which we can use during printing. *)
  let rename sharing (p:t) : t =
    let n = ref 0 in
    let new_name () = incr n; Printf.sprintf "$t%d" !n in

    match p with
    | Composite {assumptions; steps} ->
      (* now traverse again, renaming some things on the fly *)
      let new_steps = Vec.create() in

      (* traverse [t], and if there's a subterm that is shared but
         not named yet, name it now *)
      let traverse_t t : unit =
        T.iter_dag_with ~order:T.Iter_dag.Post t
          (fun u ->
              match T.Tbl.find_opt sharing.terms u with
              | Some Shared ->
                (* shared, but not named yet *)
                let name = new_name() in
                Vec.push new_steps (deft_name name u);
                T.Tbl.replace sharing.terms u (Named (N_s name))
              | _ -> ())
      in

      (* introduce naming in [step], then push it into {!new_steps} *)
      let process_step_ step =
        traverse_step_ step ~f_t:traverse_t;
        Vec.push new_steps step;
      in

      Array.iter process_step_ steps;
      composite_a ~assms:assumptions (Vec.to_array new_steps)

    | p -> p (* TODO: warning? *)
end

(** {2 Print to Quip}

    Print to a format for checking by an external tool *)
module Quip = struct
  (*
  TODO: make sure we print terms properly
  *)

  let pp_l ppx out l = Fmt.(list ~sep:(return "@ ") ppx) out l
  let pp_a ppx out l = Fmt.(array ~sep:(return "@ ") ppx) out l
  let pp_cl ~pp_t out c = Fmt.fprintf out "(@[cl@ %a@])" (pp_l (pp_lit_with ~pp_t)) c

  let rec pp_rec (sharing:Compress.sharing_info) out (self:t) : unit =
    let pp_rec = pp_rec sharing in
    let pp_t = pp_t sharing in
    let pp_cl = pp_cl ~pp_t in
    match self with
    | Unspecified -> Fmt.string out "<unspecified>"
    | Named s -> Fmt.fprintf out "(ref %s)" s
    | CC_lemma l ->
      Fmt.fprintf out "(@[cc-lemma@ %a@])" pp_cl l
    | CC_lemma_imply (l,t,u) ->
      Fmt.fprintf out "(@[cc-lemma-imply@ (@[%a@])@ (@[=@ %a@ %a@])@])"
        (pp_l pp_rec) l pp_t t pp_t u
    | Refl t -> Fmt.fprintf out "(@[refl@ %a@])" pp_t t
    | Sorry -> Fmt.string out "sorry"
    | Sorry_c c -> Fmt.fprintf out "(@[sorry-c@ %a@])" pp_cl c
    | Bool_true_is_true -> Fmt.string out "true-is-true"
    | Bool_true_neq_false -> Fmt.string out "(@[!= T F@])"
    | Bool_eq (a,b) ->
      Fmt.fprintf out "(@[bool-eq@ %a@ %a@])"
        pp_t a pp_t b
    | Bool_c (name,c) -> Fmt.fprintf out "(@[bool-c %s@ %a@])" name pp_cl c
    | Assertion t -> Fmt.fprintf out "(@[assert@ %a@])" pp_t t
    | Assertion_c c ->
      Fmt.fprintf out "(@[assert-c@ %a@])" pp_cl c
    | Hres (c, l) ->
      Fmt.fprintf out "(@[hres@ (@[init@ %a@])@ %a@])" pp_rec c
        (pp_l (pp_hres_step sharing)) l
    | DT_isa_split (ty,l) ->
      Fmt.fprintf out "(@[dt.isa.split@ (@[ty %a@])@ (@[cases@ %a@])@])"
        Ty.pp ty (pp_l pp_t) l
    | DT_isa_disj (ty,t,u) ->
      Fmt.fprintf out "(@[dt.isa.disj@ (@[ty %a@])@ %a@ %a@])"
        Ty.pp ty pp_t t pp_t u
    | DT_cstor_inj (c,i,ts,us) ->
      Fmt.fprintf out "(@[dt.cstor.inj %d@ (@[%a@ %a@])@ (@[%a@ %a@])@])"
        i Cstor.pp c (pp_l pp_t) ts Cstor.pp c (pp_l pp_t) us
    | Ite_true t -> Fmt.fprintf out "(@[ite-true@ %a@])" pp_t t
    | Ite_false t -> Fmt.fprintf out "(@[ite-false@ %a@])" pp_t t
    | LRA c -> Fmt.fprintf out "(@[lra@ %a@])" pp_cl c
    | Composite {steps; assumptions} ->
      let pp_ass out (n,a) =
        Fmt.fprintf out "(@[assuming@ (name %s) %a@])" n (pp_lit_with ~pp_t) a in
      Fmt.fprintf out "(@[steps@ (@[%a@])@ (@[<hv>%a@])@])"
        (pp_l pp_ass) assumptions (pp_a (pp_composite_step sharing)) steps

  and pp_t sharing out (t:T.t) =
    match T.Tbl.find_opt sharing.Compress.terms t with
    | Some (Named (N_s s)) ->
      Fmt.string out s (* use the newly introduced name *)
    | Some (Named (N_t t)) -> pp_t sharing out t (* use name *)
    | _ -> pp_t_noshare_root sharing out t

  and pp_t_noshare_root sharing out t =
    Base_types.pp_term_view_gen ~pp_id:ID.pp_name
      ~pp_t:(pp_t sharing) out (T.view t)

  and pp_composite_step sharing out step =
    let pp_t = pp_t sharing in
    let pp_cl = pp_cl ~pp_t in
    match step with
    | S_step_c {name;res;proof} ->
      Fmt.fprintf out "(@[stepc %s@ %a@ %a@])" name pp_cl res (pp_rec sharing) proof
    | S_define_t (c,rhs) ->
      Fmt.fprintf out "(@[deft@ %a@ %a@])"
        Term.pp c (pp_t_noshare_root sharing) rhs
    | S_define_t_name (c,rhs) ->
      Fmt.fprintf out "(@[deft@ %s@ %a@])"
        c (pp_t_noshare_root sharing) rhs

  (*
    | S_define_t (name, t) ->
      Fmt.fprintf out "(@[deft %s %a@])" name Term.pp t
  *)

  and pp_hres_step sharing out = function
    | R {pivot; p} ->
      Fmt.fprintf out "(@[r@ (@[pivot@ %a@])@ %a@])" (pp_t sharing) pivot (pp_rec sharing) p
    | R1 p -> Fmt.fprintf out "(@[r1@ %a@])"  (pp_rec sharing) p
    | P {p; lhs; rhs} ->
      Fmt.fprintf out "(@[r@ (@[lhs@ %a@])@ (@[rhs@ %a@])@ %a@])"
        (pp_t sharing) lhs (pp_t sharing) rhs (pp_rec sharing) p
    | P1 p -> Fmt.fprintf out "(@[p1@ %a@])" (pp_rec sharing) p

  (* toplevel wrapper *)
  let pp out self =
    (* find sharing *)
    let sharing = Profile.with1 "proof.find-sharing" Compress.find_sharing self in
    (* introduce names *)
    let self = Profile.with2 "proof.rename" Compress.rename sharing self in
    (* now print *)
    Fmt.fprintf out "(@[quip 1@ %a@])" (pp_rec sharing) self

  let pp_debug out self : unit =
    pp_rec Compress.no_sharing out self
end

let pp_debug = Quip.pp_debug
