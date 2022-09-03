open Sigs

module type PREPROCESS_ACTS = sig
  val proof : proof_trace
  val mk_lit : ?sign:bool -> term -> lit
  val add_clause : lit list -> step_id -> unit
  val add_lit : ?default_pol:bool -> lit -> unit
end

type preprocess_actions = (module PREPROCESS_ACTS)

(* action taken later *)
type delayed_action =
  | DA_add_clause of lit list * step_id
  | DA_add_lit of { default_pol: bool option; lit: lit }
  | DA_declare_need_th_combination of term

type t = {
  tst: Term.store;  (** state for managing terms *)
  cc: CC.t;
  proof: proof_trace;
  mutable preprocess: preprocess_hook list;
  mutable claim_term: claim_hook list;
  preprocessed: Term.t Term.Tbl.t;
  delayed_actions: delayed_action Vec.t;
  n_preprocess_clause: int Stat.counter;
}

and preprocess_hook = t -> preprocess_actions -> term -> term option
and claim_hook = Theory_id.t * (t -> term -> bool)

let create ?(stat = Stat.global) ~proof ~cc tst : t =
  {
    tst;
    proof;
    cc;
    preprocess = [];
    claim_term = [];
    preprocessed = Term.Tbl.create 8;
    delayed_actions = Vec.create ();
    n_preprocess_clause = Stat.mk_int stat "smt.preprocess.n-clauses";
  }

let on_preprocess self f = self.preprocess <- f :: self.preprocess
let on_claim self h = self.claim_term <- h :: self.claim_term

(* find what theory claims [t], unless [t] is boolean. *)
let claimed_by_ (self : t) (t : term) : Theory_id.t option =
  let ty_t = Term.ty t in

  if Term.is_bool ty_t then
    None
  else (
    match
      CCList.find_map
        (fun (th_id, f) ->
          if f self t then
            Some th_id
          else
            None)
        self.claim_term
    with
    | Some _ as r -> r
    | None ->
      Error.errorf "no theory claimed term@ `%a`@ of type `%a`" Term.pp t
        Term.pp ty_t
  )

let declare_need_th_combination (self : t) (t : term) : unit =
  Vec.push self.delayed_actions (DA_declare_need_th_combination t)

let preprocess_term_ (self : t) (t : term) : term =
  let module A = struct
    let proof = self.proof
    let mk_lit ?sign t : Lit.t = Lit.atom ?sign self.tst t

    let add_lit ?default_pol lit : unit =
      Vec.push self.delayed_actions (DA_add_lit { default_pol; lit })

    let add_clause c pr : unit =
      Vec.push self.delayed_actions (DA_add_clause (c, pr))
  end in
  let acts = (module A : PREPROCESS_ACTS) in

  (* how to preprocess a term and its subterms *)
  let rec preproc_rec_ t0 : Term.t =
    match Term.Tbl.find_opt self.preprocessed t0 with
    | Some u -> u
    | None ->
      Log.debugf 50 (fun k -> k "(@[smt.preprocess@ %a@])" Term.pp_debug t0);

      let claim_t = claimed_by_ self t0 in

      (* process sub-terms first, and find out if they are foreign in [t]  *)
      let t =
        Term.map_shallow self.tst t0 ~f:(fun _inb u ->
            let u = preproc_rec_ u in
            (match claim_t, claimed_by_ self u with
            | Some th1, Some th2 when not (Theory_id.equal th1 th2) ->
              (* [u] is foreign *)
              declare_need_th_combination self u
            | _ -> ());
            u)
      in

      (* try hooks *)
      let t =
        match CCList.find_map (fun f -> f self acts t) self.preprocess with
        | Some u ->
          (* preprocess [u], to achieve fixpoint *)
          preproc_rec_ u
        | None -> t
      in

      Term.Tbl.add self.preprocessed t0 t;

      (* signal boolean subterms, so as to decide them
         in the SAT solver *)
      if Term.is_bool (Term.ty t) then (
        Log.debugf 5 (fun k ->
            k "(@[solver.map-bool-subterm-to-lit@ :subterm %a@])" Term.pp t);

        (* ensure that SAT solver has a boolean atom for [t] *)
        let lit = Lit.atom self.tst t in
        A.add_lit lit;

        (* also map [sub] to this atom in the congruence closure, for propagation *)
        (* FIXME: use a delayed action "DA_declare_cc_lit (t, lit)" instead *)
        CC.set_as_lit self.cc (CC.add_term self.cc t) lit
      );
      t
  in
  preproc_rec_ t

(* simplify literal, then preprocess the result *)
let preproc_lit (self : t) (lit : Lit.t) : Lit.t * step_id option =
  let t = Lit.term lit in
  let sign = Lit.sign lit in

  (* FIXME: get a proof in preprocess_term_, to account for rewriting?
        or perhaps, it should only be allowed to introduce proxies so there is
        no real proof if we consider proxy definitions to be transparent


     let u, pr =
       match simplify_t self t with
       | None -> t, None
       | Some (u, pr_t_u) ->
         Log.debugf 30 (fun k ->
             k "(@[smt-solver.simplify@ :t %a@ :into %a@])" Term.pp_debug t
               Term.pp_debug u);
         u, Some pr_t_u
     in
  *)
  preprocess_term_ self u;
  Lit.atom ~sign self.tst u, pr

module type ARR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val to_list : 'a t -> 'a list
end

module Preprocess_clause (A : ARR) = struct
  (* preprocess a clause's literals, possibly emitting a proof
     for the preprocessing. *)
  let top (self : t) (c : lit A.t) (pr_c : step_id) : lit A.t * step_id =
    let steps = ref [] in

    (* simplify a literal, then preprocess it *)
    let[@inline] simp_lit lit =
      let lit, pr = simplify_and_preproc_lit self lit in
      Option.iter (fun pr -> steps := pr :: !steps) pr;
      lit
    in
    let c' = A.map simp_lit c in

    let pr_c' =
      if !steps = [] then
        pr_c
      else (
        Stat.incr self.n_preprocess_clause;
        Proof_trace.add_step self.proof @@ fun () ->
        Proof_core.lemma_rw_clause pr_c ~res:(A.to_list c') ~using:!steps
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
