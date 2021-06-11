open Base_types

module T = Term
module Ty = Ty
type term = T.t
type ty = Ty.t

type lit =
  | L_eq of bool * term * term
  | L_a of bool * term

let lit_not = function
  | L_eq (sign,a,b) -> L_eq(not sign,a,b)
  | L_a (sign,t) -> L_a (not sign,t)

let pp_lit_with ~pp_t out =
  let strsign = function true -> "+" | false -> "-" in
  function
  | L_eq (b,t,u) -> Fmt.fprintf out "(@[%s@ (@[=@ %a@ %a@])@])" (strsign b) pp_t t pp_t u
  | L_a (b,t) -> Fmt.fprintf out "(@[%s@ %a@])" (strsign b) pp_t t
let pp_lit = pp_lit_with ~pp_t:Term.pp

let lit_a t = L_a (true,t)
let lit_na t = L_a (false,t)
let lit_eq t u = L_eq (true,t,u)
let lit_neq t u = L_eq (false,t,u)
let lit_mk b t = L_a (b,t)

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
  | Bool_c of bool_c_name * term list (* boolean tautology *)
  | Nn of t (* negation normalization *)
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
let nn c : t = Nn c

let hres_l p l : t =
  let l = List.filter (function (P1 (Refl _)) -> false | _ -> true) l in
  if l=[] then p else Hres (p,l)
let hres_iter c i : t = hres_l c (Iter.to_list i)

let lra_l c : t = LRA c
let lra c = LRA (Iter.to_rev_list c)

let iter_lit ~f_t = function
  | L_eq (_,a,b) -> f_t a; f_t b
  | L_a (_,t) -> f_t t

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
  | Bool_c (_, ts) -> List.iter f_t ts
  | Nn p -> f_p p
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
  module type OUT = sig
    type out
    type printer = out -> unit
    val l : printer list -> printer
    val iter_toplist : ('a -> printer) -> 'a Iter.t -> printer
    (* list of steps, should be printed vertically if possible *)
    val a : string -> printer
  end

  (*
  TODO: make sure we print terms properly
  *)

  module Make(Out : OUT) = struct
    open Out

    let rec pp_t sharing (t:Term.t) : printer =
      match T.Tbl.find_opt sharing.Compress.terms t with
      | Some (Named (N_s s)) -> a s(* use the newly introduced name *)
      | Some (Named (N_t t)) -> pp_t sharing t (* use name *)
      | _ -> pp_t_nonshare_root sharing t

    and pp_t_nonshare_root sharing t =
      let pp_t = pp_t sharing in
      match Term.view t with
      | Bool true -> a"true"
      | Bool false -> a"false"
      | App_fun (c, args) when IArray.is_empty args -> a (ID.to_string (id_of_fun c))
      | App_fun (c, args) ->
        l(a (ID.to_string (id_of_fun c)) :: IArray.to_list_map pp_t args)
      | Eq (t,u) -> l[a"=";pp_t t;pp_t u]
      | Not u -> l[a"not";pp_t u]
      | Ite (t1,t2,t3) -> l[a"ite";pp_t t1;pp_t t2;pp_t t3]
      | LRA lra ->
        begin match lra with
          | LRA_pred (p, t1, t2) -> l[a (string_of_lra_pred p); pp_t t1; pp_t t2]
          | LRA_op (p, t1, t2) -> l[a (string_of_lra_op p); pp_t t1; pp_t t2]
          | LRA_mult (n, x) -> l[a"lra.*"; a(Q.to_string n);pp_t x]
          | LRA_const q -> a(Q.to_string q)
          | LRA_simplex_var v -> pp_t v
          | LRA_simplex_pred (v, op, q) ->
            l[a(Sidekick_arith_lra.S_op.to_string op); pp_t v; a(Q.to_string q)]
          | LRA_other x -> pp_t x
        end

    let rec pp_ty ty : printer =
      match Ty.view ty with
      | Ty_bool -> a"Bool"
      | Ty_real -> a"Real"
      | Ty_atomic {def;args=[];finite=_} ->
        let id = Ty.id_of_def def in
        a(ID.to_string id)
      | Ty_atomic {def;args;finite=_} ->
        let id = Ty.id_of_def def in
        l(a(ID.to_string id)::List.map pp_ty args)

    let pp_l ppx xs = l (List.map ppx xs)
    let pp_lit ~pp_t lit = match lit with
      | L_a(b,t) -> l[a(if b then"+" else"-");pp_t t]
      | L_eq(b,t,u) -> l[a(if b then"+" else"-");l[a"=";pp_t t;pp_t u]]
    let pp_cl ~pp_t c =
      l (a "cl" :: List.map (pp_lit ~pp_t) c)

    let rec pp_rec (sharing:Compress.sharing_info) (self:t) : printer =
      let pp_rec = pp_rec sharing in
      let pp_t = pp_t sharing in
      let pp_cl = pp_cl ~pp_t in
      match self with
      | Unspecified -> a "<unspecified>"
      | Named s -> l[a "@"; a s]
      | CC_lemma c -> l[a"ccl"; pp_cl c]
      | CC_lemma_imply (hyps,t,u) ->
        l[a"ccli"; pp_l pp_rec hyps; pp_t t; pp_t u]
      | Refl t -> l[a"refl"; pp_t t]
      | Sorry -> a"sorry"
      | Sorry_c c -> l[a"sorry-c"; pp_cl c]
      | Bool_true_is_true -> a"true-is-true"
      | Bool_true_neq_false -> a"true-neq-false"
      | Bool_eq (t1,t2) -> l[a"bool-eq";pp_t t1;pp_t t2]
      | Bool_c (name,ts) -> l(a"bool-c" :: a name :: List.map pp_t ts)
      | Nn p -> l[a"nn";pp_rec p]
      | Assertion t -> l[a"assert";pp_t t]
      | Assertion_c c -> l[a"assert-c";pp_cl c]
      | Hres (c, steps) -> l[a"hres";pp_rec c;l(List.map (pp_hres_step sharing) steps)]
      | DT_isa_split (ty,cs) ->
        l[a"dt.isa.split";pp_ty ty;l(a"cases"::List.map pp_t cs)]
      | DT_isa_disj (ty,t,u) ->
        l[a"dt.isa.disj";pp_ty ty;pp_t t;pp_t u]
      | DT_cstor_inj (c,i,ts,us) ->
        l[a"dt.cstor.inj";a(ID.to_string(Cstor.id c));
          a(string_of_int i); l(List.map pp_t ts); l(List.map pp_t us)]
      | Ite_true t -> l[a"ite-true"; pp_t t]
      | Ite_false t -> l[a"ite-false"; pp_t t]
      | LRA c -> l[a"lra";pp_cl c]
      | Composite {steps; assumptions} ->
        let pp_ass (n,ass) : printer =
          l[a"assuming";a n;pp_lit ~pp_t ass] in
        l[a"steps";l(List.map pp_ass assumptions);
          iter_toplist (pp_composite_step sharing) (Iter.of_array steps)]

    and pp_composite_step sharing step : printer =
      let pp_t = pp_t sharing in
      let pp_cl = pp_cl ~pp_t in
      match step with
      | S_step_c {name;res;proof} ->
        l[a"stepc";a name;pp_cl res;pp_rec sharing proof]
      | S_define_t (c,rhs) ->
        (* disable sharing for [rhs], otherwise it'd print [c] *)
        l[a"deft";pp_t c; pp_t_nonshare_root sharing rhs]
      | S_define_t_name (c,rhs) ->
        l[a"deft";a c; pp_t_nonshare_root sharing rhs]

    (*
      | S_define_t (name, t) ->
        Fmt.fprintf out "(@[deft %s %a@])" name Term.pp t
    *)

    and pp_hres_step sharing = function
      | R {pivot; p} -> l[a"r";pp_t sharing pivot; pp_rec sharing p]
      | R1 p -> l[a"r1";pp_rec sharing p]
      | P {p; lhs; rhs} ->
        l[a"r"; pp_t sharing lhs; pp_t sharing rhs; pp_rec sharing p]
      | P1 p -> l[a"p1"; pp_rec sharing p]

    (* toplevel wrapper *)
    let pp self : printer =
      (* find sharing *)
      let sharing = Profile.with1 "proof.find-sharing" Compress.find_sharing self in
      (* introduce names *)
      let self = Profile.with2 "proof.rename" Compress.rename sharing self in
      (* now print *)
      l[a"quip"; a"1"; pp_rec sharing self]

    let pp_debug ~sharing self : printer =
      if sharing then pp self
      else pp_rec Compress.no_sharing self
  end

  module Out_csexp = struct
    type out = out_channel
    type printer = out -> unit
    let l prs out =
      output_char out '(';
      List.iter (fun x->x out) prs;
      output_char out ')'
    let a s out = Printf.fprintf out "%d:%s" (String.length s) s
    let iter_toplist f it out =
      output_char out '(';
      it (fun x -> f x out);
      output_char out ')'
  end

  module Out_sexp = struct
    type out = out_channel
    type printer = out -> unit
    let l prs out =
      output_char out '(';
      List.iteri (fun i x->if i>0 then output_char out ' ';x out) prs;
      output_char out ')'
    let a =
      let buf = Buffer.create 128 in
      fun s out ->
        Buffer.clear buf;
        CCSexp.to_buf buf (`Atom s);
        Buffer.output_buffer out buf
    let iter_toplist f it out =
      output_char out '(';
      let first=ref true in
      it (fun x -> if !first then first := false else output_char out '\n'; f x out);
      output_char out ')'
  end

  let output oc (self:t) : unit =
    (* canonical sexp *)
    if true then (
      let module M = Make(Out_sexp) in M.pp self oc
    ) else (
      let module M = Make(Out_csexp) in M.pp self oc
    )
end

let pp_debug ~sharing out p =
  let module Out = struct
    type out = Format.formatter
    type printer = out -> unit
    let l prs out =
      Fmt.fprintf out "(@[";
      List.iteri(fun i x -> if i>0 then Fmt.fprintf out "@ "; x out) prs;
      Fmt.fprintf out "@])"
    let a s out = Fmt.string out s
    let iter_toplist f it out =
      Fmt.fprintf out "(@[<v>";
      let first=ref true in
      it (fun x -> if !first then first := false else Fmt.fprintf out "@ "; f x out);
      Fmt.fprintf out "@])"
  end
  in
  let module M = Quip.Make(Out) in
  M.pp_debug ~sharing p out
