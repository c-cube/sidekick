open Sigs

module type PREPROCESS_ACTS = sig
  val proof_tracer : Proof.Tracer.t
  val mk_lit : ?sign:bool -> term -> lit
  val add_clause : lit list -> step_id -> unit
  val add_lit : ?default_pol:bool -> lit -> unit
end

type preprocess_actions = (module PREPROCESS_ACTS)

type t = {
  tst: Term.store;  (** state for managing terms *)
  cc: CC.t;
  simplify: Simplify.t;
  proof: Proof.Tracer.t;
  mutable preprocess: preprocess_hook list;
  preprocessed: Term.t Term.Tbl.t;
  n_preprocess_clause: int Stat.counter;
}

and preprocess_hook =
  t ->
  is_sub:bool ->
  recurse:(term -> term) ->
  preprocess_actions ->
  term ->
  term option

let create ?(stat = Stat.global) ~proof ~cc ~simplify tst : t =
  let proof = (proof : #Proof.Tracer.t :> Proof.Tracer.t) in
  {
    tst;
    proof;
    cc;
    simplify;
    preprocess = [];
    preprocessed = Term.Tbl.create 8;
    n_preprocess_clause = Stat.mk_int stat "smt.preprocess.n-clauses";
  }

let on_preprocess self f = self.preprocess <- f :: self.preprocess
let cc self = self.cc

let preprocess_term_ (self : t) acts (t : term) : term =
  (* how to preprocess a term and its subterms *)
  let rec preproc_rec_ ~is_sub t0 : Term.t =
    match Term.Tbl.find_opt self.preprocessed t0 with
    | Some u -> u
    | None ->
      Log.debugf 50 (fun k -> k "(@[smt.preprocess@ %a@])" Term.pp t0);

      (* try hooks first *)
      let t =
        match
          CCList.find_map
            (fun f ->
              f self ~is_sub ~recurse:(preproc_rec_ ~is_sub:true) acts t0)
            self.preprocess
        with
        | Some u ->
          (* only accept a box (with possible side effect: new clauses, etc.) *)
          Log.debugf 20 (fun k ->
              k "(@[smt.preprocess.tr@ %a@ :into %a@])" Term.pp t0 Term.pp u);
          assert (Term.(equal (ty t0) (ty u)));
          u
        | None ->
          (* just preprocess subterms *)
          Term.map_shallow self.tst t0 ~f:(fun _inb u ->
              let u = preproc_rec_ ~is_sub:true u in
              (* TODO: is it automatically subject to TH combination?
                    probably not, if hooks let this recurse by default (e.g. UF or data)

                 (match claim_t, claimed_by_ self u with
                 | Some th1, Some th2 when not (Theory_id.equal th1 th2) ->
                   (* [u] is foreign *)
                   declare_need_th_combination self u
                 | _ -> ());
              *)
              u)
      in

      Term.Tbl.add self.preprocessed t0 t;
      t
  in
  preproc_rec_ ~is_sub:false t

(* preprocess the literal. The result must be logically equivalent;
   as a rule of thumb, it should be the same term inside except with
   some [box] added whenever a theory frontier is crossed. *)
let simplify_and_preproc_lit (self : t) acts (lit : Lit.t) :
    Lit.t * step_id option =
  let t = Lit.term lit in
  let sign = Lit.sign lit in

  let u, pr =
    match Simplify.normalize self.simplify t with
    | None -> t, None
    | Some (u, pr_t_u) ->
      Log.debugf 30 (fun k ->
          k "(@[smt-solver.simplify@ :t %a@ :into %a@])" Term.pp t Term.pp u);
      u, Some pr_t_u
  in
  assert (Term.is_bool @@ Term.ty u);
  let v = preprocess_term_ self acts u in
  Lit.atom ~sign self.tst v, pr

module type ARR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val to_list : 'a t -> 'a list
end

module Preprocess_clause (A : ARR) = struct
  (* preprocess a clause's literals, possibly emitting a proof
     for the preprocessing. *)
  let top (self : t) acts (c : lit A.t) (pr_c : step_id) : lit A.t * step_id =
    let steps = ref [] in

    (* simplify a literal, then preprocess it *)
    let[@inline] simp_lit lit =
      let lit, pr = simplify_and_preproc_lit self acts lit in
      Option.iter (fun pr -> steps := pr :: !steps) pr;
      lit
    in
    let c' = A.map simp_lit c in

    let pr_c' =
      if !steps = [] then
        pr_c
      else (
        Stat.incr self.n_preprocess_clause;
        Proof.Tracer.add_step self.proof @@ fun () ->
        Proof.Core_rules.lemma_rw_clause pr_c ~res:(A.to_list c') ~using:!steps
      )
    in
    c', pr_c'
end

module PC_list = Preprocess_clause (struct
  type 'a t = 'a list

  let map = CCList.map
  let to_list l = l
end)

module PC_arr = Preprocess_clause (CCArray)

let preprocess_clause = PC_list.top
let preprocess_clause_array = PC_arr.top
