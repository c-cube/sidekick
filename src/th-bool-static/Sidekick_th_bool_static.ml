open Sidekick_core
module Intf = Intf
open Intf
module SI = SMT.Solver_internal
module T = Term

module type ARG = Intf.ARG

module Make (A : ARG) : sig
  val theory : SMT.theory
end = struct
  type state = { tst: T.store; gensym: A.Gensym.t }

  let create tst : state = { tst; gensym = A.Gensym.create tst }
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
        ~res:[ Lit.atom (A.mk_bool tst (B_eq (a, b))) ]
    in

    let[@inline] ret u = Some (u, Iter.of_list !steps) in
    (* proof is [t <=> u] *)
    let ret_bequiv t1 u =
      add_step_ @@ mk_step_ @@ A.P.lemma_bool_equiv t1 u;
      ret u
    in

    match A.view_as_bool t with
    | B_bool _ -> None
    | B_not u when is_true u -> ret_bequiv t (T.false_ tst)
    | B_not u when is_false u -> ret_bequiv t (T.true_ tst)
    | B_not _ -> None
    | B_opaque_bool _ -> None
    | B_and a ->
      if Iter.exists is_false a then
        ret (T.false_ tst)
      else if Iter.for_all is_true a then
        ret (T.true_ tst)
      else
        None
    | B_or a ->
      if Iter.exists is_true a then
        ret (T.true_ tst)
      else if Iter.for_all is_false a then
        ret (T.false_ tst)
      else
        None
    | B_imply (args, u) ->
      if Iter.exists is_false args then
        ret (T.true_ tst)
      else if is_true u then
        ret (T.true_ tst)
      else
        None
    | B_ite (a, b, c) ->
      (* directly simplify [a] so that maybe we never will simplify one
         of the branches *)
      let a, prf_a = Simplify.normalize_t simp a in
      Option.iter add_step_ prf_a;
      (match A.view_as_bool a with
      | B_bool true ->
        add_step_eq t b ~using:(Option.to_list prf_a)
          ~c0:(mk_step_ @@ A.P.lemma_ite_true ~ite:t);
        ret b
      | B_bool false ->
        add_step_eq t c ~using:(Option.to_list prf_a)
          ~c0:(mk_step_ @@ A.P.lemma_ite_false ~ite:t);
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
    | B_atom _ -> None

  let fresh_term self ~for_t ~pre ty =
    let u = A.Gensym.fresh_term self.gensym ~pre ty in
    Log.debugf 20 (fun k ->
        k "(@[sidekick.bool.proxy@ :t %a@ :for %a@])" T.pp_debug u T.pp_debug
          for_t);
    assert (Term.equal ty (T.ty u));
    u

  let fresh_lit (self : state) ~for_t ~mk_lit ~pre : T.t * Lit.t =
    let proxy = fresh_term ~for_t ~pre self (Term.bool self.tst) in
    proxy, mk_lit proxy

  (* TODO: polarity? *)
  let cnf (self : state) (si : SI.t) (module PA : SI.PREPROCESS_ACTS) (t : T.t)
      : unit =
    Log.debugf 50 (fun k -> k "(@[th-bool.cnf@ %a@])" T.pp_debug t);
    let[@inline] mk_step_ r = Proof_trace.add_step PA.proof r in

    (* handle boolean equality *)
    let equiv_ _si ~is_xor ~t t_a t_b : unit =
      let a = PA.mk_lit t_a in
      let b = PA.mk_lit t_b in
      let a =
        if is_xor then
          Lit.neg a
        else
          a
      in
      (* [a xor b] is [(¬a) = b] *)
      let lit = PA.mk_lit t in

      (* proxy => a<=> b,
         ¬proxy => a xor b *)
      PA.add_clause
        [ Lit.neg lit; Lit.neg a; b ]
        (if is_xor then
          mk_step_ @@ A.P.lemma_bool_c "xor-e+" [ t ]
        else
          mk_step_ @@ A.P.lemma_bool_c "eq-e" [ t; t_a ]);
      PA.add_clause
        [ Lit.neg lit; Lit.neg b; a ]
        (if is_xor then
          mk_step_ @@ A.P.lemma_bool_c "xor-e-" [ t ]
        else
          mk_step_ @@ A.P.lemma_bool_c "eq-e" [ t; t_b ]);
      PA.add_clause [ lit; a; b ]
        (if is_xor then
          mk_step_ @@ A.P.lemma_bool_c "xor-i" [ t; t_a ]
        else
          mk_step_ @@ A.P.lemma_bool_c "eq-i+" [ t ]);
      PA.add_clause
        [ lit; Lit.neg a; Lit.neg b ]
        (if is_xor then
          mk_step_ @@ A.P.lemma_bool_c "xor-i" [ t; t_b ]
        else
          mk_step_ @@ A.P.lemma_bool_c "eq-i-" [ t ])
    in

    (* make a literal for [t], with a proof of [|- abs(t) = abs(lit)] *)
    (match A.view_as_bool t with
    | B_opaque_bool _ -> ()
    | B_bool _ -> ()
    | B_not _ -> ()
    | B_and l ->
      let t_subs = Iter.to_list l in
      let lit = PA.mk_lit t in
      let subs = List.map PA.mk_lit t_subs in

      (* add clauses *)
      List.iter2
        (fun t_u u ->
          PA.add_clause
            [ Lit.neg lit; u ]
            (mk_step_ @@ A.P.lemma_bool_c "and-e" [ t; t_u ]))
        t_subs subs;
      PA.add_clause
        (lit :: List.map Lit.neg subs)
        (mk_step_ @@ A.P.lemma_bool_c "and-i" [ t ])
    | B_or l ->
      let t_subs = Iter.to_list l in
      let subs = List.map PA.mk_lit t_subs in
      let lit = PA.mk_lit t in

      (* add clauses *)
      List.iter2
        (fun t_u u ->
          PA.add_clause
            [ Lit.neg u; lit ]
            (mk_step_ @@ A.P.lemma_bool_c "or-i" [ t; t_u ]))
        t_subs subs;
      PA.add_clause (Lit.neg lit :: subs)
        (mk_step_ @@ A.P.lemma_bool_c "or-e" [ t ])
    | B_imply (t_args, t_u) ->
      (* transform into [¬args \/ u] on the fly *)
      let t_args = Iter.to_list t_args in
      let args = List.map (fun t -> Lit.neg (PA.mk_lit t)) t_args in
      let u = PA.mk_lit t_u in
      let subs = u :: args in

      (* now the or-encoding *)
      let lit = PA.mk_lit t in

      (* add clauses *)
      List.iter2
        (fun t_u u ->
          PA.add_clause
            [ Lit.neg u; lit ]
            (mk_step_ @@ A.P.lemma_bool_c "imp-i" [ t; t_u ]))
        (t_u :: t_args) subs;
      PA.add_clause (Lit.neg lit :: subs)
        (mk_step_ @@ A.P.lemma_bool_c "imp-e" [ t ])
    | B_ite (a, b, c) ->
      let lit_a = PA.mk_lit a in
      PA.add_clause
        [ Lit.neg lit_a; PA.mk_lit (eq self.tst t b) ]
        (mk_step_ @@ A.P.lemma_ite_true ~ite:t);
      PA.add_clause
        [ lit_a; PA.mk_lit (eq self.tst t c) ]
        (mk_step_ @@ A.P.lemma_ite_false ~ite:t)
    | B_eq _ | B_neq _ -> ()
    | B_equiv (a, b) -> equiv_ si ~t ~is_xor:false a b
    | B_xor (a, b) -> equiv_ si ~t ~is_xor:true a b
    | B_atom _ -> ());
    ()

  let create_and_setup si =
    Log.debug 2 "(th-bool.setup)";
    let st = create (SI.tst si) in
    SI.add_simplifier si (simplify st);
    SI.on_preprocess si (cnf st);
    st

  let theory = SMT.Solver.mk_theory ~name:"th-bool" ~create_and_setup ()
end

let theory (module A : ARG) : SMT.theory =
  let module M = Make (A) in
  M.theory
