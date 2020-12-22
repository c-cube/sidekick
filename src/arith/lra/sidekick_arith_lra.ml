
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

open Sidekick_core

module Simplex = Simplex
module Predicate = Predicate
module Linear_expr = Linear_expr

type pred = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq
type op = Plus | Minus

type 'a lra_view =
  | LRA_pred of pred * 'a * 'a
  | LRA_op of op * 'a * 'a
  | LRA_mult of Q.t * 'a
  | LRA_const of Q.t
  | LRA_other of 'a

let map_view f (l:_ lra_view) : _ lra_view =
  begin match l with
    | LRA_pred (p, a, b) -> LRA_pred (p, f a, f b)
    | LRA_op (p, a, b) -> LRA_op (p, f a, f b)
    | LRA_mult (n,a) -> LRA_mult (n, f a)
    | LRA_const q -> LRA_const q
    | LRA_other x -> LRA_other (f x)
  end

module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.T.Term.t
  type ty = S.T.Ty.t

  val view_as_lra : term -> term lra_view
  (** Project the term into the theory view *)

  val mk_lra : S.T.Term.state -> term lra_view -> term
  (** Make a term from the given theory view *)

  val ty_lra : S.T.Term.state -> ty

  val has_ty_real : term -> bool
  (** Does this term have the type [Real] *)

  module Gensym : sig
    type t

    val create : S.T.Term.state -> t

    val tst : t -> S.T.Term.state

    val copy : t -> t

    val fresh_term : t -> pre:string -> S.T.Ty.t -> term
    (** Make a fresh term of the given type *)
  end
end

module type S = sig
  module A : ARG

  type state

  val create : A.S.T.Term.state -> state

  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module Ty = A.S.T.Ty
  module T = A.S.T.Term
  module Lit = A.S.Solver_internal.Lit
  module SI = A.S.Solver_internal
  module N = A.S.Solver_internal.CC.N

  module Tag = struct
    type t =
      | By_def
      | Lit of Lit.t
      | CC_eq of N.t * N.t

    let pp out = function
      | By_def -> Fmt.string out "<bydef>"
      | Lit l -> Fmt.fprintf out "(@[lit %a@])" Lit.pp l
      | CC_eq (n1,n2) -> Fmt.fprintf out "(@[cc-eq@ %a@ %a@])" N.pp n1 N.pp n2

    let to_lits si = function
      | By_def -> []
      | Lit l -> [l]
      | CC_eq (n1,n2) ->
        SI.CC.explain_eq (SI.cc si) n1 n2
  end

  module SimpVar
    : Linear_expr.VAR_GEN
      with type t = A.term
       and type Fresh.t = A.Gensym.t
       and type lit = Tag.t
  = struct
    type t = A.term
    let pp = A.S.T.Term.pp
    let compare = A.S.T.Term.compare
    type lit = Tag.t
    let pp_lit = Tag.pp
    module Fresh = struct
      type t = A.Gensym.t
      let copy = A.Gensym.copy
      let fresh (st:t) =
        let ty = A.ty_lra (A.Gensym.tst st) in
        A.Gensym.fresh_term ~pre:"_lra" st ty
    end
  end

  module SimpSolver = Simplex.Make_full(SimpVar)

  (* linear expressions *)
  module LComb = SimpSolver.L.Comb
  module LE = SimpSolver.L.Expr
  module LConstr = SimpSolver.L.Constr

  type proxy = T.t
  type state = {
    tst: T.state;
    simps: T.t T.Tbl.t; (* cache *)
    gensym: A.Gensym.t;
    neq_encoded: unit T.Tbl.t;
    (* if [a != b] asserted and not in this table, add clause [a = b \/ a<b \/ a>b] *)
    needs_th_combination: LE.t T.Tbl.t; (* terms that require theory combination *)
    t_defs: LE.t T.Tbl.t; (* term definitions *)
    pred_defs: (pred * LE.t * LE.t * T.t * T.t) T.Tbl.t; (* predicate definitions *)
    local_eqs: (N.t * N.t) Backtrack_stack.t; (* inferred by the congruence closure *)
  }

  let create tst : state =
    { tst;
      simps=T.Tbl.create 128;
      gensym=A.Gensym.create tst;
      neq_encoded=T.Tbl.create 16;
      needs_th_combination=T.Tbl.create 8;
      t_defs=T.Tbl.create 8;
      pred_defs=T.Tbl.create 16;
      local_eqs = Backtrack_stack.create();
    }

  let push_level self =
    Backtrack_stack.push_level self.local_eqs;
    ()

  let pop_levels self n =
    Backtrack_stack.pop_levels self.local_eqs n ~f:(fun _ -> ());
    ()

  (* FIXME
  let simplify (self:state) (simp:SI.Simplify.t) (t:T.t) : T.t option =
    let tst = self.tst in
    match A.view_as_bool t with
    | B_bool _ -> None
    | B_not u when is_true u -> Some (T.bool tst false)
    | B_not u when is_false u -> Some (T.bool tst true)
    | B_not _ -> None
    | B_opaque_bool _ -> None
    | B_and a ->
      if IArray.exists is_false a then Some (T.bool tst false)
      else if IArray.for_all is_true a then Some (T.bool tst true)
      else None
    | B_or a ->
      if IArray.exists is_true a then Some (T.bool tst true)
      else if IArray.for_all is_false a then Some (T.bool tst false)
      else None
    | B_imply (args, u) ->
      (* turn into a disjunction *)
      let u =
        or_a tst @@
        IArray.append (IArray.map (not_ tst) args) (IArray.singleton u)
      in
      Some u
    | B_ite (a,b,c) ->
      (* directly simplify [a] so that maybe we never will simplify one
         of the branches *)
      let a = SI.Simplify.normalize simp a in
      begin match A.view_as_bool a with
        | B_bool true -> Some b
        | B_bool false -> Some c
        | _ ->
          None
      end
    | B_equiv (a,b) when is_true a -> Some b
    | B_equiv (a,b) when is_false a -> Some (not_ tst b)
    | B_equiv (a,b) when is_true b -> Some a
    | B_equiv (a,b) when is_false b -> Some (not_ tst a)
    | B_equiv _ -> None
    | B_eq (a,b) when T.equal a b -> Some (T.bool tst true)
    | B_eq _ -> None
    | B_atom _ -> None
     *)

  let fresh_term self ~pre ty = A.Gensym.fresh_term self.gensym ~pre ty
  let fresh_lit (self:state) ~mk_lit ~pre : Lit.t =
    let t = fresh_term ~pre self Ty.bool in
    mk_lit t

  let pp_pred_def out (p,l1,l2) : unit =
    Fmt.fprintf out "(@[%a@ :l1 %a@ :l2 %a@])" Predicate.pp p LE.pp l1 LE.pp l2

  (* turn the term into a linear expression. Apply [f] on leaves. *)
  let rec as_linexp ~f (t:T.t) : LE.t =
    let open LE.Infix in
    match A.view_as_lra t with
    | LRA_other _ -> LE.monomial1 (f t)
    | LRA_pred _ ->
      Error.errorf "type error: in linexp, LRA predicate %a" T.pp t
    | LRA_op (op, t1, t2) ->
      let t1 = as_linexp ~f t1 in
      let t2 = as_linexp ~f t2 in
      begin match op with
        | Plus -> t1 + t2
        | Minus -> t1 - t2
      end
    | LRA_mult (n, x) ->
      let t = as_linexp ~f x in
      LE.( n * t )
    | LRA_const q -> LE.of_const q

  let as_linexp_id = as_linexp ~f:CCFun.id

  (* TODO: keep the linexps until they're asserted;
     TODO: but use simplification in preprocess
     *)

  (* preprocess linear expressions away *)
  let preproc_lra (self:state) si ~recurse ~mk_lit:_ ~add_clause:_ (t:T.t) : T.t option =
    Log.debugf 50 (fun k->k "lra.preprocess %a" T.pp t);
    let tst = SI.tst si in
    match A.view_as_lra t with
    | LRA_pred ((Eq|Neq) as pred, t1, t2) ->
      (* keep equality as is, needed for congruence closure *)
      let t1 = recurse t1 in
      let t2 = recurse t2 in
      let u = A.mk_lra tst (LRA_pred (pred, t1, t2)) in
      if T.equal t u then None else Some u
    | LRA_pred (pred, t1, t2) ->
      let l1 = as_linexp ~f:recurse t1 in
      let l2 = as_linexp ~f:recurse t2 in
      let proxy = fresh_term self ~pre:"_pred_lra_" Ty.bool in
      T.Tbl.add self.pred_defs proxy (pred, l1, l2, t1, t2);
      Log.debugf 5 (fun k->k"@[<hv2>lra.preprocess.step %a@ :into %a@ :def %a@]"
                       T.pp t T.pp proxy pp_pred_def (pred,l1,l2));
      Some proxy
    | LRA_op _ | LRA_mult _ ->
      let le = as_linexp ~f:recurse t in
      let proxy = fresh_term self ~pre:"_e_lra_" (T.ty t) in
      T.Tbl.add self.t_defs proxy le;
      T.Tbl.add self.needs_th_combination proxy le;
      Log.debugf 5 (fun k->k"@[<hv2>lra.preprocess.step %a@ :into %a@ :def %a@]"
                       T.pp t T.pp proxy LE.pp le);
      Some proxy
    | LRA_other t when A.has_ty_real t ->
      let le = LE.monomial1 t in
      T.Tbl.replace self.needs_th_combination t le;
      None
    | LRA_const _ | LRA_other _ -> None

  (* ensure that [a != b] triggers the clause
     [a=b \/ a<b \/ a>b] *)
  let encode_neq self si acts trail : unit =
    let tst = self.tst in
    begin
      trail
      |> Iter.filter_map
        (fun lit ->
           let t = Lit.term lit in
           Log.debugf 50 (fun k->k "@[lra: check lit %a@ :t %a@ :sign %B@]"
                             Lit.pp lit T.pp t (Lit.sign lit));

           let check_pred pred a b =
             let pred = if Lit.sign lit then pred else Predicate.neg pred in
             Log.debugf 50 (fun k->k "pred = `%s`" (Predicate.to_string pred));
             if pred = Neq && not (T.Tbl.mem self.neq_encoded t) then (
               Some (lit, a, b)
             ) else None
           in

           begin match T.Tbl.find self.pred_defs t with
             | (pred, _, _, ta, tb) -> check_pred pred ta tb
             | exception Not_found ->
               begin match A.view_as_lra t with
                 | LRA_pred (pred, a, b) -> check_pred pred a b
                 | _ -> None
               end
           end)
      |> Iter.iter
        (fun (lit,a,b) ->
           Log.debugf 50 (fun k->k "encode neq in %a" Lit.pp lit);
           let c = [
             Lit.neg lit;
             SI.mk_lit si acts (A.mk_lra tst (LRA_pred (Lt, a, b)));
             SI.mk_lit si acts (A.mk_lra tst (LRA_pred (Lt, b, a)));
           ] in
           SI.add_clause_permanent si acts c;
           T.Tbl.add self.neq_encoded (Lit.term (Lit.abs lit)) ();
        )
    end

  let dedup_lits lits : _ list =
    let module LTbl = CCHashtbl.Make(Lit) in
    let tbl = LTbl.create 16 in
    List.iter (fun l -> LTbl.replace tbl l ()) lits;
    LTbl.keys_list tbl

  module Q_map = CCMap.Make(Q)

  let final_check_ (self:state) si (acts:SI.actions) (trail:_ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
    let simplex = SimpSolver.create self.gensym in
    encode_neq self si acts trail;
    (* first, add definitions *)
    begin
      T.Tbl.iter
        (fun t le ->
           let open LE.Infix in
           let le = le - LE.monomial1 t in
           let c = LConstr.eq0 le in
           let lit = Tag.By_def in
           SimpSolver.add_constr simplex c lit
        )
        self.t_defs
    end;
    (* add congruence closure equalities *)
    Backtrack_stack.iter self.local_eqs
      ~f:(fun (n1,n2) ->
         let t1 = N.term n1 |> as_linexp_id in
         let t2 = N.term n2 |> as_linexp_id in
         let c = LConstr.eq0 LE.(t1 -  t2) in
         let lit = Tag.CC_eq (n1,n2) in
         SimpSolver.add_constr simplex c lit);
    (* add trail *)
    begin
      trail
      |> Iter.iter
        (fun lit ->
           let sign = Lit.sign lit in
           let t = Lit.term lit in
           let assert_pred pred a b =
             let pred = if sign then pred else Predicate.neg pred in
             if pred = Neq then (
               Log.debugf 50 (fun k->k "(@[LRA.skip-neq@ :in %a@])" T.pp t);
             ) else (
               let c = LConstr.of_expr LE.(a-b) pred in
               SimpSolver.add_constr simplex c (Tag.Lit lit);
             )
           in
           begin match T.Tbl.find self.pred_defs t with
             | (pred, a, b, _, _) -> assert_pred pred a b
             | exception Not_found ->
               begin match A.view_as_lra t with
                 | LRA_pred (pred, a, b) ->
                   let a = try T.Tbl.find self.t_defs a with _ -> as_linexp_id a in
                   let b = try T.Tbl.find self.t_defs b with _ -> as_linexp_id b in
                   assert_pred pred a b
                 | _ -> ()
               end
           end)
    end;
    Log.debug 5 "lra: call arith solver";
    begin match SimpSolver.solve simplex with
      | SimpSolver.Solution _m ->
        Log.debug 5 "lra: solver returns SAT";
        Log.debugf 50
          (fun k->k "(@[LRA.needs-th-combination:@ %a@])"
              (Util.pp_iter @@ Fmt.within "`" "`" T.pp) (T.Tbl.keys self.needs_th_combination));
        (* FIXME: theory combination
        let lazy model = model in
        Log.debugf 30 (fun k->k "(@[LRA.model@ %a@])" FM_A.pp_model model);

        (* theory combination: for [t1,t2] terms in [self.needs_th_combination]
           that have same value, but are not provably equal, push
           decision [t1=t2] into the SAT solver. *)
        begin
          let by_val: T.t list Q_map.t =
            T.Tbl.to_iter self.needs_th_combination
            |> Iter.map (fun (t,le) -> FM_A.eval_model model le, t)
            |> Iter.fold
              (fun m (q,t) ->
                 let l = Q_map.get_or ~default:[] q m in
                 Q_map.add q (t::l) m)
              Q_map.empty
          in
          Q_map.iter
            (fun _q ts ->
               begin match ts with
                 | [] | [_] -> ()
                 | ts ->
                   (* several terms! see if they are already equal *)
                   CCList.diagonal ts
                   |> List.iter
                     (fun (t1,t2) ->
                        Log.debugf 50
                          (fun k->k "(@[LRA.th-comb.check-pair[val=%a]@ %a@ %a@])"
                              Q.pp_print _q T.pp t1 T.pp t2);
                        (* FIXME: we need these equalities to be considered
                           by the congruence closure *)
                        if not (SI.cc_are_equal si t1 t2) then (
                          Log.debug 50 "LRA.th-comb.must-decide-equal";
                          let t = A.mk_lra (SI.tst si) (LRA_pred (Eq, t1, t2)) in
                          let lit = SI.mk_lit si acts t in
                          SI.push_decision si acts lit
                        )
                     )
               end)
            by_val;
          ()
        end;
           *)
        ()
      | SimpSolver.Unsatisfiable cert ->
        let unsat_core =
          match SimpSolver.check_cert simplex cert with
          | `Ok unsat_core -> unsat_core (* TODO *)
          | _ -> assert false (* some kind of fatal error ? *)
        in
        Log.debugf 5 (fun k->k"lra: solver returns UNSAT@ with cert %a"
                         (Fmt.Dump.list Tag.pp) unsat_core);
        (* TODO: produce and store a proper LRA resolution proof *)
        let confl =
          unsat_core
          |> Iter.of_list
          |> Iter.flat_map_l (fun tag -> Tag.to_lits si tag)
          |> Iter.map Lit.neg
          |> Iter.to_rev_list
        in
        SI.raise_conflict si acts confl SI.P.default
    end;
    ()

  let create_and_setup si =
    Log.debug 2 "(th-lra.setup)";
    let st = create (SI.tst si) in
    (* TODO    SI.add_simplifier si (simplify st); *)
    SI.add_preprocess si (preproc_lra st);
    SI.on_final_check si (final_check_ st);
    SI.on_cc_post_merge si
      (fun _ _ n1 n2 ->
         if A.has_ty_real (N.term n1) then (
           Backtrack_stack.push st.local_eqs (n1, n2)
         ));
    (*     SI.add_preprocess si (cnf st); *)
    (* TODO: theory combination *)
    st

  let theory =
    A.S.mk_theory
      ~name:"th-lra"
      ~create_and_setup ~push_level ~pop_levels
      ()
end
