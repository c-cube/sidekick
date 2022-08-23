open Sidekick_core
module Intf = Intf
open Intf
module SI = SMT.Solver_internal
module Proof_rules = Proof_rules
module T = Term

module type ARG = Intf.ARG

(** Theory with dynamic reduction to clauses *)
module Make (A : ARG) : sig
  val theory : SMT.theory
end = struct
  (* TODO (long term): relevancy propagation *)

  type term = T.t

  type state = {
    tst: T.store;
    expanded: unit Lit.Tbl.t; (* set of literals already expanded *)
    n_simplify: int Stat.counter;
    n_expanded: int Stat.counter;
    n_clauses: int Stat.counter;
  }

  let create ~stat tst : state =
    {
      tst;
      expanded = Lit.Tbl.create 256;
      n_simplify = Stat.mk_int stat "th.bool.simplified";
      n_expanded = Stat.mk_int stat "th.bool.expanded";
      n_clauses = Stat.mk_int stat "th.bool.clauses";
    }

  let[@inline] not_ tst t = A.mk_bool tst (B_not t)
  let[@inline] eq tst a b = A.mk_bool tst (B_eq (a, b))
  let pp_c_ = Fmt.Dump.list Lit.pp

  let is_true t =
    match T.as_bool_val t with
    | Some true -> true
    | _ -> false

  let is_false t =
    match T.as_bool_val t with
    | Some false -> true
    | _ -> false

  (* TODO: share this with th-bool-static by way of a library for
     boolean simplification? (also handle one-point rule and the likes) *)
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
    | B_and (a, b) ->
      if is_false a || is_false b then
        ret (T.false_ tst)
      else if is_true a && is_true b then
        ret (T.true_ tst)
      else
        None
    | B_or (a, b) ->
      if is_true a || is_true b then
        ret (T.true_ tst)
      else if is_false a && is_false b then
        ret (T.false_ tst)
      else
        None
    | B_imply (a, b) ->
      if is_false a || is_true b then
        ret (T.true_ tst)
      else if is_true a && is_false b then
        ret (T.false_ tst)
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

  let[@inline] expanded self lit = Lit.Tbl.mem self.expanded lit

  let set_expanded self lit : unit =
    if not (expanded self lit) then (
      Stat.incr self.n_expanded;
      Lit.Tbl.add self.expanded lit ()
    )

  (* preprocess. *)
  let preprocess_ (self : state) (_si : SI.t) (module PA : SI.PREPROCESS_ACTS)
      (t : T.t) : unit =
    Log.debugf 50 (fun k -> k "(@[th-bool.dny.preprocess@ %a@])" T.pp_debug t);
    let[@inline] mk_step_ r = Proof_trace.add_step PA.proof r in

    (match A.view_as_bool t with
    | B_ite (a, b, c) ->
      let lit_a = PA.mk_lit a in
      Stat.incr self.n_clauses;
      PA.add_clause
        [ Lit.neg lit_a; PA.mk_lit (eq self.tst t b) ]
        (mk_step_ @@ fun () -> Proof_rules.lemma_ite_true ~ite:t);

      Stat.incr self.n_clauses;
      PA.add_clause
        [ lit_a; PA.mk_lit (eq self.tst t c) ]
        (mk_step_ @@ fun () -> Proof_rules.lemma_ite_false ~ite:t)
    | _ -> ());
    ()

  let tseitin ~final:_ (self : state) solver (acts : SI.theory_actions)
      (lit : Lit.t) (t : term) (v : term bool_view) : unit =
    Log.debugf 50 (fun k -> k "(@[th-bool-dyn.tseitin@ %a@])" Lit.pp lit);

    let add_axiom c pr : unit =
      Log.debugf 50 (fun k ->
          k "(@[th-bool-dyn.add-axiom@ %a@ :expanding %a@])" pp_c_ c Lit.pp lit);
      Stat.incr self.n_clauses;
      set_expanded self lit;
      SI.add_clause_permanent solver acts c pr
    in

    let[@inline] mk_step_ r = Proof_trace.add_step (SI.proof solver) r in

    (* handle boolean equality *)
    let equiv_ ~is_xor a b : unit =
      (* [a xor b] is [(¬a) = b] *)
      let a =
        if is_xor then
          Lit.neg a
        else
          a
      in

      (* [lit => a<=> b],
         [¬lit => a xor b] *)
      add_axiom
        [ Lit.neg lit; Lit.neg a; b ]
        (if is_xor then
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "xor-e+" [ t ]
        else
          mk_step_ @@ fun () ->
          Proof_rules.lemma_bool_c "eq-e" [ t; Lit.term a ]);

      add_axiom
        [ Lit.neg lit; Lit.neg b; a ]
        (if is_xor then
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "xor-e-" [ t ]
        else
          mk_step_ @@ fun () ->
          Proof_rules.lemma_bool_c "eq-e" [ t; Lit.term b ]);

      add_axiom [ lit; a; b ]
        (if is_xor then
          mk_step_ @@ fun () ->
          Proof_rules.lemma_bool_c "xor-i" [ t; Lit.term a ]
        else
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "eq-i+" [ t ]);

      add_axiom
        [ lit; Lit.neg a; Lit.neg b ]
        (if is_xor then
          mk_step_ @@ fun () ->
          Proof_rules.lemma_bool_c "xor-i" [ t; Lit.term b ]
        else
          mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "eq-i-" [ t ])
    in

    match v with
    | B_not _ -> ()
    | B_atom _ -> () (* CC will manage *)
    | B_bool true -> ()
    | B_bool false ->
      SI.add_clause_permanent solver acts
        [ Lit.neg lit ]
        (mk_step_ @@ fun () -> Proof_core.lemma_true (Lit.term lit))
    | _ when expanded self lit -> () (* already done *)
    | B_and (a, b) ->
      let subs = List.map (Lit.atom self.tst) [ a; b ] in

      if Lit.sign lit then
        (* assert [(and …t_i) => t_i] *)
        List.iter
          (fun sub ->
            add_axiom
              [ Lit.neg lit; sub ]
              ( mk_step_ @@ fun () ->
                Proof_rules.lemma_bool_c "and-e" [ t; Lit.term sub ] ))
          subs
      else (
        (* axiom [¬(and …t_i)=> \/_i (¬ t_i)], only in final-check *)
        let c = Lit.neg lit :: List.map Lit.neg subs in
        add_axiom c
          (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "and-i" [ t ])
      )
    | B_or (a, b) ->
      let subs = List.map (Lit.atom self.tst) [ a; b ] in

      if not @@ Lit.sign lit then
        (* propagate [¬sub_i \/ lit] *)
        List.iter
          (fun sub ->
            add_axiom
              [ Lit.neg lit; Lit.neg sub ]
              ( mk_step_ @@ fun () ->
                Proof_rules.lemma_bool_c "or-i" [ t; Lit.term sub ] ))
          subs
      else (
        (* axiom [lit => \/_i subs_i] *)
        let c = Lit.neg lit :: subs in
        add_axiom c (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "or-e" [ t ])
      )
    | B_imply (a, b) ->
      let a = Lit.atom self.tst a in
      let b = Lit.atom self.tst b in
      if Lit.sign lit then (
        (* axiom [lit => a => b] *)
        let c = [ Lit.neg lit; Lit.neg a; b ] in
        add_axiom c
          (mk_step_ @@ fun () -> Proof_rules.lemma_bool_c "imp-e" [ t ])
      ) else if not @@ Lit.sign lit then (
        (* propagate [¬ lit => ¬b] and [¬lit => a] *)
        add_axiom
          [ a; Lit.neg lit ]
          ( mk_step_ @@ fun () ->
            Proof_rules.lemma_bool_c "imp-i" [ t; Lit.term a ] );

        add_axiom
          [ Lit.neg b; Lit.neg lit ]
          ( mk_step_ @@ fun () ->
            Proof_rules.lemma_bool_c "imp-i" [ t; Lit.term b ] )
      )
    | B_ite (a, b, c) ->
      assert (T.is_bool b);
      (* boolean ite:
         just add [a => (ite a b c <=> b)]
         and [¬a => (ite a b c <=> c)] *)
      let lit_a = Lit.atom self.tst a in
      add_axiom
        [ Lit.neg lit_a; Lit.make_eq self.tst t b ]
        (mk_step_ @@ fun () -> Proof_rules.lemma_ite_true ~ite:t);
      add_axiom
        [ Lit.neg lit; lit_a; Lit.make_eq self.tst t c ]
        (mk_step_ @@ fun () -> Proof_rules.lemma_ite_false ~ite:t)
    | B_equiv (a, b) ->
      let a = Lit.atom self.tst a in
      let b = Lit.atom self.tst b in
      equiv_ ~is_xor:false a b
    | B_eq (a, b) when T.is_bool a ->
      let a = Lit.atom self.tst a in
      let b = Lit.atom self.tst b in
      equiv_ ~is_xor:false a b
    | B_xor (a, b) ->
      let a = Lit.atom self.tst a in
      let b = Lit.atom self.tst b in
      equiv_ ~is_xor:true a b
    | B_neq (a, b) when T.is_bool a ->
      let a = Lit.atom self.tst a in
      let b = Lit.atom self.tst b in
      equiv_ ~is_xor:true a b
    | B_eq _ | B_neq _ -> ()

  let check_ ~final self solver acts lits =
    lits (fun lit ->
        let t = Lit.term lit in
        match A.view_as_bool t with
        | B_atom _ -> ()
        | v -> tseitin ~final self solver acts lit t v)

  let partial_check (self : state) solver acts (lits : Lit.t Iter.t) =
    check_ ~final:false self solver acts lits

  let final_check (self : state) solver acts (lits : Lit.t Iter.t) =
    check_ ~final:true self solver acts lits

  let create_and_setup (solver : SI.t) : state =
    let tst = SI.tst solver in
    let stat = SI.stats solver in
    let self =
      {
        tst;
        expanded = Lit.Tbl.create 24;
        n_expanded = Stat.mk_int stat "th.bool.dyn.expanded";
        n_clauses = Stat.mk_int stat "th.bool.dyn.clauses";
        n_simplify = Stat.mk_int stat "th.bool.dyn.simplify";
      }
    in
    SI.add_simplifier solver (simplify self);
    SI.on_preprocess solver (preprocess_ self);
    SI.on_final_check solver (final_check self);
    SI.on_partial_check solver (partial_check self);
    self

  let theory = SMT.Solver.mk_theory ~name:"th-bool.dyn" ~create_and_setup ()
end

let theory (module A : ARG) : SMT.theory =
  let module M = Make (A) in
  M.theory
