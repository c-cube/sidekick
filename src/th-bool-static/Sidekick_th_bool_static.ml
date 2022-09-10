open Sidekick_core
module Intf = Intf
open Intf
module SI = SMT.Solver_internal
module Proof_rules = Proof_rules
module T = Term

module type ARG = Intf.ARG

module Make (A : ARG) : sig
  val theory : SMT.theory
end = struct
  type state = {
    tst: T.store;
    gensym: Gensym.t;
    n_simplify: int Stat.counter;
    n_clauses: int Stat.counter;
  }

  let create ~stat tst : state =
    {
      tst;
      gensym = Gensym.create tst;
      n_simplify = Stat.mk_int stat "th.bool.simplified";
      n_clauses = Stat.mk_int stat "th.bool.cnf-clauses";
    }

  let[@inline] not_ tst t = A.mk_bool tst (B_not t)
  let[@inline] eq tst a b = A.mk_bool tst (B_eq (a, b))

  let is_true t =
    match T.as_bool_val t with
    | Some true -> true
    | _ -> false

  let is_false t =
    match T.as_bool_val t with
    | Some false -> true
    | _ -> false

  let unfold_and t : T.Set.t =
    let rec aux acc t =
      match A.view_as_bool t with
      | B_and l -> List.fold_left aux acc l
      | _ -> T.Set.add t acc
    in
    aux T.Set.empty t

  let unfold_or t : T.Set.t =
    let rec aux acc t =
      match A.view_as_bool t with
      | B_or l -> List.fold_left aux acc l
      | _ -> T.Set.add t acc
    in
    aux T.Set.empty t

  let simplify (self : state) (simp : Simplify.t) (t : T.t) :
      (T.t * Proof_step.id Iter.t) option =
    let tst = self.tst in

    let proof = Simplify.proof simp in
    let steps = ref [] in
    let add_step_ s = steps := s :: !steps in
    let mk_step_ r = Proof_trace.add_step proof r in

    let add_step_eq a b ~using ~c0 : unit =
      add_step_ @@ mk_step_
      @@ fun () ->
      Proof_core.lemma_rw_clause c0 ~using
        ~res:[ Lit.atom tst (A.mk_bool tst (B_eq (a, b))) ]
    in

    let[@inline] ret u =
      Stat.incr self.n_simplify;
      Some (u, Iter.of_list !steps)
    in

    (* proof is [t <=> u] *)
    let ret_bequiv t1 u =
      (add_step_ @@ mk_step_ @@ fun () -> Proof_rules.lemma_bool_equiv t1 u);
      ret u
    in

    match A.view_as_bool t with
    | B_bool _ -> None
    | B_not u when is_true u -> ret_bequiv t (T.false_ tst)
    | B_not u when is_false u -> ret_bequiv t (T.true_ tst)
    | B_not _ -> None
    | B_atom _ -> None
    | B_and _ ->
      let set = unfold_and t in
      if T.Set.exists is_false set then
        ret (T.false_ tst)
      else if T.Set.for_all is_true set then
        ret (T.true_ tst)
      else (
        let t' = A.mk_bool tst (B_and (T.Set.to_list set)) in
        if not (T.equal t t') then
          ret_bequiv t t'
        else
          None
      )
    | B_or _ ->
      let set = unfold_or t in
      if T.Set.exists is_true set then
        ret (T.true_ tst)
      else if T.Set.for_all is_false set then
        ret (T.false_ tst)
      else (
        let t' = A.mk_bool tst (B_or (T.Set.to_list set)) in
        if not (T.equal t t') then
          ret_bequiv t t'
        else
          None
      )
    | B_imply (a, b) ->
      (* always rewrite [a => b] to [¬a \/ b] *)
      let u = A.mk_bool tst (B_or [ T.not tst a; b ]) in
      ret u
    | B_ite (a, b, c) ->
      (* directly simplify [a] so that maybe we never will simplify one
         of the branches *)
      let a, prf_a = Simplify.normalize_t simp a in
      Option.iter add_step_ prf_a;
      (match A.view_as_bool a with
      | B_bool true ->
        add_step_eq t b ~using:(Option.to_list prf_a)
          ~c0:(mk_step_ @@ fun () -> Proof_rules.lemma_ite_true ~ite:t);
        ret b
      | B_bool false ->
        add_step_eq t c ~using:(Option.to_list prf_a)
          ~c0:(mk_step_ @@ fun () -> Proof_rules.lemma_ite_false ~ite:t);
        ret c
      | _ -> None)
    | B_equiv (a, b) when is_true a -> ret_bequiv t b
    | B_equiv (a, b) when is_false a -> ret_bequiv t (not_ tst b)
    | B_equiv (a, b) when is_true b -> ret_bequiv t a
    | B_equiv (a, b) when is_false b -> ret_bequiv t (not_ tst a)
    | B_xor (a, b) when is_false a -> ret_bequiv t b
    | B_xor (a, b) when is_true a -> ret_bequiv t (not_ tst b)
    | B_xor (a, b) when is_false b -> ret_bequiv t a
    | B_xor (a, b) when is_true b -> ret_bequiv t (not_ tst a)
    | B_equiv _ | B_xor _ -> None
    | B_eq (a, b) when T.equal a b -> ret_bequiv t (T.true_ tst)
    | B_neq (a, b) when T.equal a b -> ret_bequiv t (T.true_ tst)
    | B_eq _ | B_neq _ -> None

  let fresh_term self ~for_t ~pre ty =
    let u = Gensym.fresh_term self.gensym ~pre ty in
    Log.debugf 20 (fun k ->
        k "(@[sidekick.bool.proxy@ :t %a@ :for %a@])" T.pp u T.pp for_t);
    assert (Term.equal ty (T.ty u));
    u

  let fresh_lit (self : state) ~for_t ~mk_lit ~pre : T.t * Lit.t =
    let proxy = fresh_term ~for_t ~pre self (Term.bool self.tst) in
    proxy, mk_lit proxy

  (* TODO: polarity? *)
  let cnf (self : state) (_preproc : SMT.Preprocess.t) ~is_sub:_ ~recurse
      (module PA : SI.PREPROCESS_ACTS) (t : T.t) : T.t option =
    Log.debugf 50 (fun k -> k "(@[th-bool.cnf@ %a@])" T.pp t);
    let[@inline] mk_step_ r = Proof_trace.add_step PA.proof r in

    (* handle boolean equality *)
    let equiv_ (self : state) ~is_xor ~t ~box_t t_a t_b : unit =
      let t_a = recurse t_a in
      let t_b = recurse t_b in
      let a = PA.mk_lit t_a in
      let b = PA.mk_lit t_b in
      let a =
        if is_xor then
          Lit.neg a
        else
          a
      in
      (* [a xor b] is [(¬a) = b] *)
      let lit = PA.mk_lit box_t in

      (* proxy => a<=> b,
         ¬proxy => a xor b *)
      Stat.incr self.n_clauses;
      PA.add_clause
        [ Lit.neg lit; Lit.neg a; b ]
        (if is_xor then
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "xor-e+" [ t ]
        else
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "eq-e" [ t; t_a ]);

      Stat.incr self.n_clauses;
      PA.add_clause
        [ Lit.neg lit; Lit.neg b; a ]
        (if is_xor then
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "xor-e-" [ t ]
        else
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "eq-e" [ t; t_b ]);

      Stat.incr self.n_clauses;
      PA.add_clause [ lit; a; b ]
        (if is_xor then
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "xor-i" [ t; t_a ]
        else
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "eq-i+" [ t ]);

      Stat.incr self.n_clauses;
      PA.add_clause
        [ lit; Lit.neg a; Lit.neg b ]
        (if is_xor then
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "xor-i" [ t; t_b ]
        else
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "eq-i-" [ t ])
    in

    match A.view_as_bool t with
    | B_bool _ | B_not _ -> None
    | B_and l ->
      let box_t = Box.box self.tst t in
      let l = CCList.map recurse l in
      let lit = PA.mk_lit box_t in
      let subs = List.map PA.mk_lit l in

      (* add clauses *)
      List.iter
        (fun u ->
          let t_u = Lit.term u in
          Stat.incr self.n_clauses;
          PA.add_clause
            [ Lit.neg lit; u ]
            (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "and-e" [ t; t_u ]))
        subs;

      Stat.incr self.n_clauses;
      PA.add_clause
        (lit :: List.map Lit.neg subs)
        (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "and-i" [ t ]);
      Some box_t
    | B_or l ->
      let box_t = Box.box self.tst t in
      let l = CCList.map recurse l in
      let subs = List.map PA.mk_lit l in
      let lit = PA.mk_lit box_t in

      (* add clauses *)
      List.iter
        (fun u ->
          let t_u = Lit.term u in
          Stat.incr self.n_clauses;
          PA.add_clause
            [ Lit.neg u; lit ]
            (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "or-i" [ t; t_u ]))
        subs;

      Stat.incr self.n_clauses;
      PA.add_clause (Lit.neg lit :: subs)
        (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "or-e" [ t ]);
      Some box_t
    | B_imply (a, b) ->
      (* transform into [¬a \/ b] on the fly *)
      let box_t = Box.box self.tst t in
      let n_a = PA.mk_lit ~sign:false @@ recurse a in
      let b = PA.mk_lit @@ recurse b in
      let subs = [ n_a; b ] in

      (* now the or-encoding *)
      let lit = PA.mk_lit t in

      (* add clauses *)
      List.iter
        (fun u ->
          let t_u = Lit.term u in
          Stat.incr self.n_clauses;
          PA.add_clause
            [ Lit.neg u; lit ]
            (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "imp-i" [ t; t_u ]))
        subs;

      Stat.incr self.n_clauses;
      PA.add_clause (Lit.neg lit :: subs)
        (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "imp-e" [ t ]);

      Some box_t
    | B_ite (a, b, c) ->
      let box_t = Box.box self.tst t in
      let a = recurse a in
      let b = recurse b in
      let c = recurse c in

      let lit_a = PA.mk_lit a in
      Stat.incr self.n_clauses;
      PA.add_clause
        [ Lit.neg lit_a; PA.mk_lit (eq self.tst box_t b) ]
        (mk_step_ @@ fun () -> Proof_rules.lemma_ite_true ~ite:t);

      Stat.incr self.n_clauses;
      PA.add_clause
        [ lit_a; PA.mk_lit (eq self.tst box_t c) ]
        (mk_step_ @@ fun () -> Proof_rules.lemma_ite_false ~ite:t);

      Some box_t
    | B_eq _ | B_neq _ -> None
    | B_equiv (a, b) ->
      let box_t = Box.box self.tst t in
      equiv_ self ~t ~box_t ~is_xor:false a b;
      Some box_t
    | B_xor (a, b) ->
      let box_t = Box.box self.tst t in
      equiv_ self ~t ~box_t ~is_xor:true a b;
      Some box_t
    | B_atom _ -> None

  let create_and_setup ~id:_ si =
    Log.debug 2 "(th-bool.setup)";
    let st = create ~stat:(SI.stats si) (SI.tst si) in
    SI.add_simplifier si (simplify st);
    SI.on_preprocess si (cnf st);
    st

  let theory = SMT.Solver.mk_theory ~name:"th-bool.static" ~create_and_setup ()
end

let theory (module A : ARG) : SMT.theory =
  let module M = Make (A) in
  M.theory
