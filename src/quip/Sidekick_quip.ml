
module Proof = Proof
open Proof

type t = Proof.t

(** {2 Print to Quip}

    Print to a format for checking by an external tool *)

module type OUT = sig
  type out
  type printer = out -> unit
  val l : printer list -> printer
  val iter_toplist : ('a -> printer) -> 'a Iter.t -> printer
  (* list of steps, should be printed vertically if possible *)
  val a : string -> printer
end

(** Build a printer that uses {!Out} *)
module Make_printer(Out : OUT) = struct
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
    | Lit.L_a(b,t) -> l[a(if b then"+" else"-");pp_t t]
    | Lit.L_eq(b,t,u) -> l[a(if b then"+" else"-");l[a"=";pp_t t;pp_t u]]
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
    | Rup (c, hyps) ->
      l[a"rup";pp_cl c;l(List.map pp_rec hyps)]
    | Clause_rw{res; c0; using} ->
      l[a"clause-rw";pp_cl res;pp_rec c0;l(List.map pp_rec using)]
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

(** Output to canonical S-expressions *)
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

(** Output to classic S-expressions *)
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
let string_of_out_format = function
  | Sexp -> "sexp"
  | CSexp -> "csexp"
let pp_out_format out f = Fmt.string out (string_of_out_format f)

let default_out_format = Sexp

let output ?(fmt=Sexp) oc (self:t) : unit =
  match fmt with
  | Sexp ->
    let module M = Make_printer(Out_sexp) in
    M.pp self oc
  | CSexp ->
    let module M = Make_printer(Out_csexp) in
    M.pp self oc

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
  let module M = Make_printer(Out) in
  M.pp_debug p out

