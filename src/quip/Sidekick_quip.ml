
(** A reference to a previously defined object in the proof *)
type id = int

module Ty = struct
  type t =
    | Bool
    | Arrow of t array * t
    | App of string * t array
    | Ref of id

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
    | Ref id -> Fmt.fprintf out "@@%d" id
end

module Fun = struct
  type t = string
  let pp out (self:t) = Fmt.string out self
  let equal : t -> t -> bool = (=)
  let hash : t -> int = CCHash.poly
end

module Cstor = Fun

module T = struct
  type t =
    | Bool of bool
    | App_fun of Fun.t * t array
    | App_ho of t * t
    | Ite of t * t * t
    | Not of t
    | Eq of t * t
    | Ref of id
  let[@inline] view (self:t) : t = self

  let equal : t -> t -> bool = (=)
  let hash : t -> int = CCHash.poly

  let rec pp out = function
    | Bool b -> Fmt.bool out b
    | Ite (a,b,c) -> Fmt.fprintf out "(@[if@ %a@ %a@ %a@])" pp a pp b pp c
    | App_fun (f,[||]) -> Fmt.string out f
    | App_fun (f,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_array pp) args
    | App_ho (f,a) -> Fmt.fprintf out "(@[%a@ %a@])" pp f pp a
    | Not a -> Fmt.fprintf out "(@[not@ %a@])" pp a
    | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
    | Ref id -> Fmt.fprintf out "@@%d" id

  module As_key = struct
    type nonrec t = t
    let hash = hash
    let equal = equal
  end
  module Tbl = CCHashtbl.Make(As_key)
end

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

let pp_lit = pp_lit_with ~pp_t:T.pp

let lit_a t = L_a (true,t)
let lit_na t = L_a (false,t)
let lit_eq t u = L_eq (true,t,u)
let lit_neq t u = L_eq (false,t,u)
let lit_mk b t = L_a (b,t)
let lit_sign = function L_a (b,_) | L_eq (b,_,_) -> b

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
  | Drup_res of clause
  | Hres of t * hres_step list
  | Res of term * t * t
  | Res1 of t * t
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
      steps: composite_step array; (* last proof_rule is the proof *)
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

let drup_res c : t = Drup_res c
let hres_l p l : t =
  let l = List.filter (function (P1 (Refl _)) -> false | _ -> true) l in
  if l=[] then p else Hres (p,l)
let hres_iter c i : t = hres_l c (Iter.to_list i)
let res ~pivot p1 p2 : t = Res (pivot,p1,p2)
let res1 p1 p2 : t = Res1 (p1,p2)

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
  | Drup_res c -> f_clause c
  | Hres (i, l) ->
    f_p i;
    List.iter
      (function
        | R1 p -> f_p p
        | P1 p -> f_p p
        | R {pivot;p} -> f_p p; f_t pivot
        | P {lhs;rhs;p} -> f_p p; f_t lhs; f_t rhs)
      l
  | Res (t,p1,p2) -> f_t t; f_p p1; f_p p2
  | Res1 (p1,p2) -> f_p p1; f_p p2
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

    let rec pp_t t =
      match T.view t with
      | T.Bool true -> a"true"
      | T.Bool false -> a"false"
      | T.App_fun (c, [||]) -> a c
      | T.App_fun (c, args) ->
        l(a c :: Util.array_to_list_map pp_t args)
      | T.Ref i -> l[a"@"; a(string_of_int i)]
      | T.App_ho(f,a) -> l[pp_t f;pp_t a]
      | T.Eq (t,u) -> l[a"=";pp_t t;pp_t u]
      | T.Not u -> l[a"not";pp_t u]
      | T.Ite (t1,t2,t3) -> l[a"ite";pp_t t1;pp_t t2;pp_t t3]
      (*
      | T.LRA lra ->
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
         *)

    let rec pp_ty ty : printer =
      match Ty.view ty with
      | Ty.Bool -> a"Bool"
      | Ty.App (c,[||]) ->
        a c
      | Ty.App (c,args) ->
        l(a c::Util.array_to_list_map pp_ty args)
      | Ty.Ref i -> l[a "@"; a (string_of_int i)]
      | Ty.Arrow (args,b) ->
        l (a "->" :: Util.array_to_list_map pp_ty args @ [pp_ty b])

    let pp_l ppx xs = l (List.map ppx xs)
    let pp_lit ~pp_t lit = match lit with
      | L_a(b,t) -> l[a(if b then"+" else"-");pp_t t]
      | L_eq(b,t,u) -> l[a(if b then"+" else"-");l[a"=";pp_t t;pp_t u]]
    let pp_cl ~pp_t c =
      l (a "cl" :: List.map (pp_lit ~pp_t) c)

    let rec pp_rec (self:t) : printer =
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
      | Bool_true_is_true -> a"t-is-t"
      | Bool_true_neq_false -> a"t-ne-f"
      | Bool_eq (t1,t2) -> l[a"bool-eq";pp_t t1;pp_t t2]
      | Bool_c (name,ts) -> l(a"bool-c" :: a name :: List.map pp_t ts)
      | Nn p -> l[a"nn";pp_rec p]
      | Assertion t -> l[a"assert";pp_t t]
      | Assertion_c c -> l[a"assert-c";pp_cl c]
      | Drup_res c -> l[a"drup";pp_cl c]
      | Hres (c, steps) -> l[a"hres";pp_rec c;l(List.map pp_hres_step steps)]
      | Res (t,p1,p2) -> l[a"r";pp_t t;pp_rec p1;pp_rec p2]
      | Res1 (p1,p2) -> l[a"r1";pp_rec p1;pp_rec p2]
      | DT_isa_split (ty,cs) ->
        l[a"dt.isa.split";pp_ty ty;l(a"cases"::List.map pp_t cs)]
      | DT_isa_disj (ty,t,u) ->
        l[a"dt.isa.disj";pp_ty ty;pp_t t;pp_t u]
      | DT_cstor_inj (c,i,ts,us) ->
        l[a"dt.cstor.inj";a c;
          a(string_of_int i); l(List.map pp_t ts); l(List.map pp_t us)]
      | Ite_true t -> l[a"ite-true"; pp_t t]
      | Ite_false t -> l[a"ite-false"; pp_t t]
      | LRA c -> l[a"lra";pp_cl c]
      | Composite {steps; assumptions} ->
        let pp_ass (n,ass) : printer =
          l[a"assuming";a n;pp_lit ~pp_t ass] in
        l[a"steps";l(List.map pp_ass assumptions);
          iter_toplist pp_composite_step (Iter.of_array steps)]

    and pp_composite_step proof_rule : printer =
      let pp_cl = pp_cl ~pp_t in
      match proof_rule with
      | S_step_c {name;res;proof} ->
        l[a"stepc";a name;pp_cl res;pp_rec proof]
      | S_define_t (c,rhs) ->
        (* disable sharing for [rhs], otherwise it'd print [c] *)
        l[a"deft";pp_t c; pp_t rhs]
      | S_define_t_name (c,rhs) ->
        l[a"deft";a c; pp_t rhs]

    (*
      | S_define_t (name, t) ->
        Fmt.fprintf out "(@[deft %s %a@])" name Term.pp t
    *)

    and pp_hres_step = function
      | R {pivot; p} -> l[a"r";pp_t pivot; pp_rec p]
      | R1 p -> l[a"r1";pp_rec p]
      | P {p; lhs; rhs} ->
        l[a"r"; pp_t lhs; pp_t rhs; pp_rec p]
      | P1 p -> l[a"p1"; pp_rec p]

    (* toplevel wrapper *)
    let pp self : printer =
      fun out ->
      Profile.with_ "quip.print" @@ fun () ->
      l[a"quip"; a"1"; pp_rec self] out

    let pp_debug self : printer = pp self
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

  type out_format = Sexp | CSexp
  let default_out_format = Sexp

  let out_format_ = match Sys.getenv "PROOF_FMT" with
    | "csexp" -> CSexp
    | "sexp" -> Sexp
    | s -> failwith (Printf.sprintf "unknown proof format %S" s)
    | exception _ -> default_out_format

  let output oc (self:t) : unit =
    match out_format_ with
    | Sexp -> let module M = Make(Out_sexp) in M.pp self oc
    | CSexp ->
      (* canonical sexp *)
      let module M = Make(Out_csexp) in M.pp self oc
end

let pp_debug out p =
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
  M.pp_debug p out


let of_proof _ _ : t = Sorry

let output = Quip.output
