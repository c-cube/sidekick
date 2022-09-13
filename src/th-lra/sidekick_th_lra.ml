(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

open Sidekick_core
open Sidekick_cc
module Intf = Intf
include Intf
module SI = SMT.Solver_internal

module Tag = struct
  type t = Lit of Lit.t | CC_eq of E_node.t * E_node.t

  let pp out = function
    | Lit l -> Fmt.fprintf out "(@[lit %a@])" Lit.pp l
    | CC_eq (n1, n2) ->
      Fmt.fprintf out "(@[cc-eq@ %a@ %a@])" E_node.pp n1 E_node.pp n2

  let to_lits si = function
    | Lit l -> [ l ]
    | CC_eq (n1, n2) ->
      let r = CC.explain_eq (SI.cc si) n1 n2 in
      (* FIXME
         assert (not (SI.CC.Resolved_expl.is_semantic r));
      *)
      r.lits
end

module SimpVar : Linear_expr.VAR with type t = Term.t and type lit = Tag.t =
struct
  type t = Term.t

  let pp = Term.pp
  let compare = Term.compare

  type lit = Tag.t

  let pp_lit = Tag.pp

  let not_lit = function
    | Tag.Lit l -> Some (Tag.Lit (Lit.neg l))
    | _ -> None
end

module Make (A : ARG) = (* : S with module A = A *) struct
  module LE_ = Linear_expr.Make (A.Q) (SimpVar)
  module LE = LE_.Expr

  module SimpSolver = Sidekick_simplex.Make (struct
    module Z = A.Z
    module Q = A.Q
    module Var = SimpVar

    let mk_lit _ _ _ = assert false
  end)

  module Subst = SimpSolver.Subst
  module Comb_map = CCMap.Make (LE_.Comb)

  (* turn the term into a linear expression. Apply [f] on leaves. *)
  let rec as_linexp (t : Term.t) : LE.t =
    let open LE.Infix in
    match A.view_as_lra t with
    | LRA_other _ -> LE.monomial1 t
    | LRA_pred _ ->
      Error.errorf "type error: in linexp, LRA predicate %a" Term.pp t
    | LRA_op (op, t1, t2) ->
      let t1 = as_linexp t1 in
      let t2 = as_linexp t2 in
      (match op with
      | Plus -> t1 + t2
      | Minus -> t1 - t2)
    | LRA_mult (n, x) ->
      let t = as_linexp x in
      LE.(n * t)
    | LRA_const q -> LE.of_const q

  (* monoid to track linear expressions in congruence classes, to clash on merge *)
  module Monoid_exprs = struct
    let name = "lra.const"

    type state = unit

    let create _ = ()

    type single = { le: LE.t; n: E_node.t }
    type t = single list

    let pp_single out { le = _; n } = E_node.pp out n

    let pp out self =
      match self with
      | [] -> ()
      | [ x ] -> pp_single out x
      | _ -> Fmt.fprintf out "(@[exprs@ %a@])" (Util.pp_list pp_single) self

    let of_term _cc () n t =
      match A.view_as_lra t with
      | LRA_const _ | LRA_op _ | LRA_mult _ ->
        let le = as_linexp t in
        Some [ { n; le } ], []
      | LRA_other _ | LRA_pred _ -> None, []

    exception Confl of Expl.t

    (* merge lists. If two linear expressions equal up to a constant are
       merged, conflict. *)
    let merge _cc () n1 l1 n2 l2 expl_12 : _ result =
      try
        let i = Iter.(product (of_list l1) (of_list l2)) in
        i (fun (s1, s2) ->
            let le = LE.(s1.le - s2.le) in
            if LE.is_const le && not (LE.is_zero le) then (
              (* conflict: [le+c = le + d] is impossible *)
              let expl =
                let open Expl in
                mk_list [ mk_merge s1.n n1; mk_merge s2.n n2; expl_12 ]
              in
              raise (Confl expl)
            ));
        Ok (List.rev_append l1 l2, [])
      with Confl expl -> Error (CC.Handler_action.Conflict expl)
  end

  module ST_exprs = Sidekick_cc.Plugin.Make (Monoid_exprs)

  type state = {
    tst: Term.store;
    proof: Proof_trace.t;
    gensym: Gensym.t;
    in_model: unit Term.Tbl.t; (* terms to add to model *)
    encoded_eqs: unit Term.Tbl.t;
    (* [a=b] gets clause [a = b <=> (a >= b /\ a <= b)] *)
    encoded_lits: Term.t Term.Tbl.t;  (** [t => lit for t], using gensym *)
    simp_preds: (Term.t * S_op.t * A.Q.t) Term.Tbl.t;
    (* term -> its simplex meaning *)
    simp_defined: (Term.t * LE.t) Term.Tbl.t;
    (* (rational) terms that are equal to a linexp *)
    st_exprs: ST_exprs.t;
    mutable encoded_le: Term.t Comb_map.t; (* [le] -> var encoding [le] *)
    simplex: SimpSolver.t;
    mutable last_res: SimpSolver.result option;
    n_propagate: int Stat.counter;
    n_conflict: int Stat.counter;
  }

  let create (si : SI.t) : state =
    let stat = SI.stats si in
    let proof = SI.proof si in
    let tst = SI.tst si in
    {
      tst;
      proof;
      in_model = Term.Tbl.create 8;
      st_exprs = ST_exprs.create_and_setup (SI.cc si);
      gensym = Gensym.create tst;
      simp_preds = Term.Tbl.create 32;
      simp_defined = Term.Tbl.create 16;
      encoded_eqs = Term.Tbl.create 8;
      encoded_lits = Term.Tbl.create 8;
      encoded_le = Comb_map.empty;
      simplex = SimpSolver.create ~stat ();
      last_res = None;
      n_propagate = Stat.mk_int stat "th.lra.propagate";
      n_conflict = Stat.mk_int stat "th.lra.conflicts";
    }

  let[@inline] reset_res_ (self : state) : unit = self.last_res <- None
  let[@inline] n_levels self : int = ST_exprs.n_levels self.st_exprs

  let push_level self =
    ST_exprs.push_level self.st_exprs;
    SimpSolver.push_level self.simplex;
    ()

  let pop_levels self n =
    reset_res_ self;
    ST_exprs.pop_levels self.st_exprs n;
    SimpSolver.pop_levels self.simplex n;
    ()

  let fresh_term self ~pre ty = Gensym.fresh_term self.gensym ~pre ty

  let fresh_lit (self : state) ~mk_lit ~pre : Lit.t =
    let t = fresh_term ~pre self (Term.bool self.tst) in
    mk_lit t

  let pp_pred_def out (p, l1, l2) : unit =
    Fmt.fprintf out "(@[%a@ :l1 %a@ :l2 %a@])" Predicate.pp p LE.pp l1 LE.pp l2

  let[@inline] t_const self n : Term.t = A.mk_lra self.tst (LRA_const n)
  let[@inline] t_zero self : Term.t = t_const self A.Q.zero

  let[@inline] is_const_ t =
    match A.view_as_lra t with
    | LRA_const _ -> true
    | _ -> false

  let[@inline] as_const_ t =
    match A.view_as_lra t with
    | LRA_const n -> Some n
    | _ -> None

  let[@inline] is_zero t =
    match A.view_as_lra t with
    | LRA_const n -> A.Q.(n = zero)
    | _ -> false

  let t_of_comb (self : state) (comb : LE_.Comb.t) ~(init : Term.t) : Term.t =
    let[@inline] ( + ) a b = A.mk_lra self.tst (LRA_op (Plus, a, b)) in
    let[@inline] ( * ) a b = A.mk_lra self.tst (LRA_mult (a, b)) in

    let cur = ref init in
    LE_.Comb.iter
      (fun t c ->
        let tc =
          if A.Q.(c = of_int 1) then
            t
          else
            c * t
        in
        cur :=
          if is_zero !cur then
            tc
          else
            !cur + tc)
      comb;
    !cur

  (* encode back into a term *)
  let t_of_linexp (self : state) (le : LE.t) : Term.t =
    let comb = LE.comb le in
    let const = LE.const le in
    t_of_comb self comb ~init:(A.mk_lra self.tst (LRA_const const))

  (* return a variable that is equal to [le_comb] in the simplex. *)
  let var_encoding_comb ~pre self (le_comb : LE_.Comb.t) : Term.t =
    assert (not (LE_.Comb.is_empty le_comb));
    match LE_.Comb.as_singleton le_comb with
    | Some (c, x) when A.Q.(c = one) -> x (* trivial linexp *)
    | _ ->
      (match Comb_map.find le_comb self.encoded_le with
      | x -> x (* already encoded that *)
      | exception Not_found ->
        (* new variable to represent [le_comb] *)
        let proxy = fresh_term self ~pre (A.ty_real self.tst) in
        (* TODO: define proxy *)
        self.encoded_le <- Comb_map.add le_comb proxy self.encoded_le;
        Log.debugf 50 (fun k ->
            k "(@[lra.encode-linexp@ `@[%a@]`@ :into-var %a@])" LE_.Comb.pp
              le_comb Term.pp proxy);

        LE_.Comb.iter (fun v _ -> SimpSolver.add_var self.simplex v) le_comb;
        SimpSolver.define self.simplex proxy (LE_.Comb.to_list le_comb);
        proxy)

  let add_clause_lra_ ?using (module PA : SI.PREPROCESS_ACTS) lits =
    let pr =
      Proof_trace.add_step PA.proof @@ fun () -> Proof_rules.lemma_lra lits
    in
    let pr =
      match using with
      | None -> pr
      | Some using ->
        Proof_trace.add_step PA.proof @@ fun () ->
        Proof_core.lemma_rw_clause pr ~res:lits ~using
    in
    PA.add_clause lits pr

  let s_op_of_pred pred : S_op.t =
    match pred with
    | Eq | Neq -> assert false (* unreachable *)
    | Leq -> S_op.Leq
    | Lt -> S_op.Lt
    | Geq -> S_op.Geq
    | Gt -> S_op.Gt

  (* turn a linear expression into a single constant and a coeff.
     This might define a side variable in the simplex. *)
  let le_comb_to_singleton_ (self : state) (le_comb : LE_.Comb.t) :
      Term.t * A.Q.t =
    match LE_.Comb.as_singleton le_comb with
    | Some (coeff, v) -> v, coeff
    | None ->
      (* non trivial linexp, give it a fresh name in the simplex *)
      (match Comb_map.get le_comb self.encoded_le with
      | Some x -> x, A.Q.one (* already encoded that *)
      | None ->
        let proxy = fresh_term self ~pre:"_le_comb" (A.ty_real self.tst) in

        self.encoded_le <- Comb_map.add le_comb proxy self.encoded_le;
        LE_.Comb.iter (fun v _ -> SimpSolver.add_var self.simplex v) le_comb;
        SimpSolver.define self.simplex proxy (LE_.Comb.to_list le_comb);

        Log.debugf 50 (fun k ->
            k "(@[lra.encode-linexp.to-term@ `@[%a@]`@ :new-t %a@])" LE_.Comb.pp
              le_comb Term.pp proxy);

        proxy, A.Q.one)

  (* preprocess linear expressions away *)
  let preproc_lra (self : state) _preproc ~is_sub:_ ~recurse
      (module PA : SI.PREPROCESS_ACTS) (t : Term.t) : Term.t option =
    Log.debugf 50 (fun k -> k "(@[lra.preprocess@ %a@])" Term.pp t);
    let tst = self.tst in

    (* tell the CC this term exists *)
    let declare_term_to_cc ~sub:_ t =
      Log.debugf 50 (fun k -> k "(@[lra.declare-term-to-cc@ %a@])" Term.pp t);
      ignore (CC.add_term (SMT.Preprocess.cc _preproc) t : E_node.t)
    in

    match A.view_as_lra t with
    | LRA_pred (((Eq | Neq) as pred), t1, t2) when is_const_ t1 && is_const_ t2
      ->
      (* comparison of constants: can decide right now *)
      (match A.view_as_lra t1, A.view_as_lra t2 with
      | LRA_const n1, LRA_const n2 ->
        let is_eq = pred = Eq in
        let t_is_true = is_eq = A.Q.equal n1 n2 in
        let lit = PA.mk_lit ~sign:t_is_true t in
        add_clause_lra_ (module PA) [ lit ];
        None
      | _ -> assert false)
    | LRA_pred ((Eq | Neq), t1, t2) ->
      (* equality: just punt to [t1 = t2 <=> (t1 <= t2 /\ t1 >= t2)] *)
      (* TODO: box [t], recurse on [t1 <= t2] and [t1 >= t2],
         add 3 atomic clauses, return [box t] *)
      let _, t = Term.abs self.tst t in
      if not (Term.Tbl.mem self.encoded_eqs t) then (
        let u1 = recurse @@ A.mk_lra tst (LRA_pred (Leq, t1, t2)) in
        let u2 = recurse @@ A.mk_lra tst (LRA_pred (Geq, t1, t2)) in

        Term.Tbl.add self.encoded_eqs t ();

        (* encode [t <=> (u1 /\ u2)] *)
        let lit_t = PA.mk_lit t in
        let lit_u1 = PA.mk_lit u1 in
        let lit_u2 = PA.mk_lit u2 in
        add_clause_lra_ (module PA) [ Lit.neg lit_t; lit_u1 ];
        add_clause_lra_ (module PA) [ Lit.neg lit_t; lit_u2 ];
        add_clause_lra_ (module PA) [ Lit.neg lit_u1; Lit.neg lit_u2; lit_t ]
      );
      None
    | LRA_pred _ when Term.Tbl.mem self.encoded_lits t ->
      (* already encoded *)
      let u = Term.Tbl.find self.encoded_lits t in
      Some u
    | LRA_pred (pred, t1, t2) ->
      let box_t = Box.box self.tst t in
      let l1 = as_linexp t1 in
      let l2 = as_linexp t2 in
      let le = LE.(l1 - l2) |> LE.map ~f:recurse in
      let le_comb, le_const = LE.comb le, LE.const le in
      let le_const = A.Q.neg le_const in
      let op = s_op_of_pred pred in

      (* now we have [le_comb op le_const] *)

      (* obtain a single variable for the linear combination *)
      let v, c_v = le_comb_to_singleton_ self le_comb in
      declare_term_to_cc ~sub:false v;
      LE_.Comb.iter (fun v _ -> declare_term_to_cc ~sub:true v) le_comb;

      (* turn into simplex constraint. For example,
         [c . v <= const] becomes a direct simplex constraint [v <= const/c]
         (beware the sign) *)

      (* make sure to swap sides if multiplying with a negative coeff *)
      let q = A.Q.(le_const / c_v) in
      let op =
        if A.Q.(c_v < zero) then
          S_op.neg_sign op
        else
          op
      in

      let lit = PA.mk_lit ~sign:true box_t in
      let constr = SimpSolver.Constraint.mk v op q in
      SimpSolver.declare_bound self.simplex constr (Tag.Lit lit);
      Term.Tbl.add self.simp_preds box_t (v, op, q);
      Term.Tbl.add self.encoded_lits box_t box_t;

      Log.debugf 50 (fun k ->
          k "(@[lra.preprocess.pred@ :t %a@ :to-constr %a@])" Term.pp t
            SimpSolver.Constraint.pp constr);

      Some box_t
    | LRA_op _ | LRA_mult _ ->
      (match Term.Tbl.find_opt self.simp_defined t with
      | Some (t, _le) -> Some t
      | None ->
        let box_t = Box.box self.tst t in
        (* we define these terms so their value in the model make sense *)
        let le = as_linexp t |> LE.map ~f:recurse in
        Term.Tbl.add self.simp_defined t (box_t, le);
        Some box_t)
    | LRA_const _n -> None
    | LRA_other _ -> None

  let find_foreign (acts : SMT.Find_foreign.actions) ~is_sub (t : Term.t) : unit
      =
    if A.has_ty_real t && is_sub then (
      let (module FA : SMT.Find_foreign.ACTIONS) = acts in
      FA.declare_need_th_combination t
    )

  let simplify (self : state) (_recurse : _) (t : Term.t) :
      (Term.t * Proof_step.id Iter.t) option =
    let proof_eq t u =
      Proof_trace.add_step self.proof @@ fun () ->
      Proof_rules.lemma_lra [ Lit.atom self.tst (Term.eq self.tst t u) ]
    in
    let proof_bool t ~sign:b =
      let lit = Lit.atom ~sign:b self.tst t in
      Proof_trace.add_step self.proof @@ fun () -> Proof_rules.lemma_lra [ lit ]
    in

    match A.view_as_lra t with
    | LRA_op _ | LRA_mult _ ->
      let le = as_linexp t in
      if LE.is_const le then (
        let c = LE.const le in
        let u = A.mk_lra self.tst (LRA_const c) in
        let pr = proof_eq t u in
        Some (u, Iter.return pr)
      ) else (
        let u = t_of_linexp self le in
        if t != u then (
          let pr = proof_eq t u in
          Some (u, Iter.return pr)
        ) else
          None
      )
    | LRA_pred ((Eq | Neq), _, _) ->
      (* never change equalities, it can affect theory combination *)
      None
    | LRA_pred (pred, l1, l2) ->
      let le = LE.(as_linexp l1 - as_linexp l2) in

      if LE.is_const le then (
        let c = LE.const le in
        let is_true =
          match pred with
          | Leq -> A.Q.(c <= zero)
          | Geq -> A.Q.(c >= zero)
          | Lt -> A.Q.(c < zero)
          | Gt -> A.Q.(c > zero)
          | Eq -> A.Q.(c = zero)
          | Neq -> A.Q.(c <> zero)
        in
        let u = Term.bool_val self.tst is_true in
        let pr = proof_bool t ~sign:is_true in
        Some (u, Iter.return pr)
      ) else (
        (* le <= const *)
        let u =
          A.mk_lra self.tst
            (LRA_pred
               ( pred,
                 t_of_comb self (LE.comb le) ~init:(t_zero self),
                 t_const self (A.Q.neg @@ LE.const le) ))
        in

        if t != u then (
          let pr = proof_eq t u in
          Some (u, Iter.return pr)
        ) else
          None
      )
    | _ -> None

  (* raise conflict from certificate *)
  let fail_with_cert (self : state) si acts cert : 'a =
    Profile.with1 "lra.simplex.check-cert" SimpSolver._check_cert cert;
    let confl =
      SimpSolver.Unsat_cert.lits cert
      |> CCList.flat_map (Tag.to_lits si)
      |> List.rev_map Lit.neg
    in
    let pr =
      Proof_trace.add_step (SI.proof si) @@ fun () ->
      Proof_rules.lemma_lra confl
    in
    Stat.incr self.n_conflict;
    SI.raise_conflict si acts confl pr

  let on_propagate_ self si acts lit ~reason =
    match lit with
    | Tag.Lit lit ->
      (* TODO: more detailed proof certificate *)
      Stat.incr self.n_propagate;
      SI.propagate si acts lit ~reason:(fun () ->
          let lits = CCList.flat_map (Tag.to_lits si) reason in
          let pr =
            Proof_trace.add_step (SI.proof si) @@ fun () ->
            Proof_rules.lemma_lra (lit :: lits)
          in
          CCList.flat_map (Tag.to_lits si) reason, pr)
    | _ -> ()

  (** Check satisfiability of simplex, and sets [self.last_res] *)
  let check_simplex_ self si acts : SimpSolver.Subst.t =
    Log.debugf 5 (fun k ->
        k "(@[lra.check-simplex@ :n-vars %d :n-rows %d@])"
          (SimpSolver.n_vars self.simplex)
          (SimpSolver.n_rows self.simplex));
    let res =
      Profile.with_ "lra.simplex.solve" @@ fun () ->
      SimpSolver.check self.simplex ~on_propagate:(on_propagate_ self si acts)
    in
    Log.debug 5 "(lra.check-simplex.done)";
    self.last_res <- Some res;
    match res with
    | SimpSolver.Sat m -> m
    | SimpSolver.Unsat cert ->
      Log.debugf 10 (fun k ->
          k "(@[lra.check.unsat@ :cert %a@])" SimpSolver.Unsat_cert.pp cert);
      fail_with_cert self si acts cert

  (* TODO: trivial propagations *)

  let add_local_eq_t (self : state) si acts t1 t2 ~tag : unit =
    Log.debugf 20 (fun k ->
        k "(@[lra.add-local-eq@ %a@ %a@])" Term.pp t1 Term.pp t2);
    reset_res_ self;
    let t1, t2 =
      if Term.compare t1 t2 > 0 then
        t2, t1
      else
        t1, t2
    in

    let le = LE.(as_linexp t1 - as_linexp t2) in
    let le_comb, le_const = LE.comb le, LE.const le in
    let le_const = A.Q.neg le_const in

    if LE_.Comb.is_empty le_comb then (
      if A.Q.(le_const <> zero) then (
        (* [c=0] when [c] is not 0 *)
        let lit = Lit.atom ~sign:false self.tst @@ Term.eq self.tst t1 t2 in
        let pr =
          Proof_trace.add_step self.proof @@ fun () ->
          Proof_rules.lemma_lra [ lit ]
        in
        SI.add_clause_permanent si acts [ lit ] pr
      )
    ) else (
      let v = var_encoding_comb ~pre:"le_local_eq" self le_comb in
      try
        let c1 = SimpSolver.Constraint.geq v le_const in
        SimpSolver.add_constraint self.simplex c1 tag
          ~on_propagate:(on_propagate_ self si acts);
        let c2 = SimpSolver.Constraint.leq v le_const in
        SimpSolver.add_constraint self.simplex c2 tag
          ~on_propagate:(on_propagate_ self si acts)
      with SimpSolver.E_unsat cert -> fail_with_cert self si acts cert
    )

  let add_local_eq (self : state) si acts n1 n2 : unit =
    let t1 = E_node.term n1 in
    let t2 = E_node.term n2 in
    add_local_eq_t self si acts t1 t2 ~tag:(Tag.CC_eq (n1, n2))

  (* evaluate a term directly, as a variable *)
  let eval_in_subst_ subst t =
    match A.view_as_lra t with
    | LRA_const n -> n
    | _ -> Subst.eval subst t |> Option.value ~default:A.Q.zero

  (* evaluate a linear expression *)
  let eval_le_in_subst_ subst (le : LE.t) = LE.eval (eval_in_subst_ subst) le

  (* FIXME: rework into model creation
     let do_th_combination (self : state) _si _acts : _ Iter.t =
       Log.debug 1 "(lra.do-th-combinations)";
       let model =
         match self.last_res with
         | Some (SimpSolver.Sat m) -> m
         | _ -> assert false
       in

       let vals = Subst.to_iter model |> Term.Tbl.of_iter in

       (* also include terms that occur under function symbols, if they're
          not in the model already *)
       Term.Tbl.iter
         (fun t () ->
           if not (Term.Tbl.mem vals t) then (
             let v = eval_in_subst_ model t in
             Term.Tbl.add vals t v
           ))
         self.needs_th_combination;

       (* also consider subterms that are linear expressions,
          and evaluate them using the value of each variable
          in that linear expression. For example a term [a + 2b]
          is evaluated as [eval(a) + 2 × eval(b)]. *)
       Term.Tbl.iter
         (fun t le ->
           if not (Term.Tbl.mem vals t) then (
             let v = eval_le_in_subst_ model le in
             Term.Tbl.add vals t v
           ))
         self.simp_defined;

       (* return whole model *)
       Term.Tbl.to_iter vals |> Iter.map (fun (t, v) -> t, t_const self v)
  *)

  let add_trail_lit_ ~changed self si acts (lit : Lit.t) : unit =
    let sign = Lit.sign lit in
    let lit_t = Lit.term lit in
    match Term.Tbl.get self.simp_preds lit_t, A.view_as_lra lit_t with
    | Some (v, op, q), _ ->
      Log.debugf 50 (fun k ->
          k "(@[lra.partial-check.add@ :lit %a@ :lit-t %a@])" Lit.pp lit Term.pp
            lit_t);

      (* need to account for the literal's sign *)
      let op =
        if sign then
          op
        else
          S_op.not_ op
      in

      (* assert new constraint to Simplex *)
      let constr = SimpSolver.Constraint.mk v op q in
      Log.debugf 10 (fun k ->
          k "(@[lra.partial-check.assert@ %a@])" SimpSolver.Constraint.pp constr);
      changed := true;
      (try
         SimpSolver.add_var self.simplex v;
         SimpSolver.add_constraint self.simplex constr (Tag.Lit lit)
           ~on_propagate:(on_propagate_ self si acts)
       with SimpSolver.E_unsat cert ->
         Log.debugf 10 (fun k ->
             k "(@[lra.partial-check.unsat@ :cert %a@])"
               SimpSolver.Unsat_cert.pp cert);
         fail_with_cert self si acts cert)
    | None, LRA_pred (Eq, t1, t2) when sign ->
      add_local_eq_t self si acts t1 t2 ~tag:(Tag.Lit lit)
    | None, LRA_pred (Neq, t1, t2) when not sign ->
      add_local_eq_t self si acts t1 t2 ~tag:(Tag.Lit lit)
    | None, _ -> ()

  (* partial checks is where we add literals from the trail to the
     simplex. *)
  let partial_check_ self si acts trail : unit =
    Profile.with_ "lra.partial-check" @@ fun () ->
    reset_res_ self;
    let changed = ref false in

    Iter.iter (add_trail_lit_ self si acts ~changed) trail;

    (* incremental check *)
    if !changed then ignore (check_simplex_ self si acts : SimpSolver.Subst.t);
    ()

  let final_check_ (self : state) si (acts : SI.theory_actions)
      (trail : _ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
    Profile.with_ "lra.final-check" @@ fun () ->
    reset_res_ self;

    let changed = ref false in
    Iter.iter (add_trail_lit_ ~changed self si acts) trail;

    ST_exprs.iter_all self.st_exprs (fun (_, l) ->
        Iter.diagonal_l l (fun (s1, s2) -> add_local_eq self si acts s1.n s2.n));

    (* TODO: jiggle model to reduce the number of variables that
       have the same value *)
    let model = check_simplex_ self si acts in
    Log.debugf 20 (fun k -> k "(@[lra.model@ %a@])" SimpSolver.Subst.pp model);
    Log.debug 5 "(lra: solver returns SAT)";
    ()

  (* help generating model *)
  let model_ask_ (self : state) _si _model (t : Term.t) : _ option =
    let res =
      match self.last_res with
      | Some (SimpSolver.Sat m) ->
        Log.debugf 50 (fun k -> k "(@[lra.model-ask@ %a@])" Term.pp t);
        (match A.view_as_lra t with
        | LRA_const n -> Some n (* always eval constants to themselves *)
        | _ -> SimpSolver.V_map.get t m)
        |> Option.map (fun t -> t_const self t, [])
      | _ -> None
    in
    match res with
    | Some _ -> res
    | None when A.has_ty_real t ->
      (* last resort: return 0 *)
      (* NOTE: this should go away maybe? no term should escape the LRA model… *)
      Log.debugf 0 (fun k -> k "MODEL TY REAL DEFAULT %a" Term.pp t);
      let zero = A.mk_lra self.tst (LRA_const A.Q.zero) in
      Some (zero, [])
    | None -> None

  (* help generating model *)
  let model_complete_ (self : state) _si ~add : unit =
    Log.debugf 30 (fun k -> k "(lra.model-complete)");
    match self.last_res with
    | Some (SimpSolver.Sat m) when Term.Tbl.length self.in_model > 0 ->
      Log.debugf 50 (fun k ->
          k "(@[lra.in_model@ %a@])" (Util.pp_iter Term.pp)
            (Term.Tbl.keys self.in_model));

      let add_t t () =
        match SimpSolver.V_map.get t m with
        | None -> ()
        | Some u -> add t (t_const self u)
      in
      Term.Tbl.iter add_t self.in_model
    | _ -> ()

  let k_state = SMT.Registry.create_key ()

  let create_and_setup ~id:_ si =
    Log.debug 2 "(th-lra.setup)";
    let st = create si in
    SMT.Registry.set (SI.registry si) k_state st;
    SI.add_simplifier si (simplify st);
    SI.on_preprocess si (preproc_lra st);
    SI.on_find_foreign si find_foreign;
    SI.on_final_check si (final_check_ st);
    (* SI.on_partial_check si (partial_check_ st); *)
    SI.on_model si ~ask:(model_ask_ st) ~complete:(model_complete_ st);
    SI.on_cc_pre_merge si (fun (_cc, n1, n2, expl) ->
        match as_const_ (E_node.term n1), as_const_ (E_node.term n2) with
        | Some q1, Some q2 when A.Q.(q1 <> q2) ->
          (* classes with incompatible constants *)
          Log.debugf 30 (fun k ->
              k "(@[lra.merge-incompatible-consts@ %a@ %a@])" E_node.pp n1
                E_node.pp n2);
          Error (CC.Handler_action.Conflict expl)
        | _ -> Ok []);
    st

  let theory =
    SMT.Solver.mk_theory ~name:"th-lra" ~create_and_setup ~push_level
      ~pop_levels ()
end

let theory (module A : ARG) : SMT.theory =
  let module M = Make (A) in
  M.theory
