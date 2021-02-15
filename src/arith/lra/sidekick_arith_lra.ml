
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

open Sidekick_core

module Simplex2 = Simplex2
module Predicate = Predicate
module Linear_expr = Linear_expr

module S_op = Simplex2.Op

type pred = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq
type op = Plus | Minus

type 'a lra_view =
  | LRA_pred of pred * 'a * 'a
  | LRA_op of op * 'a * 'a
  | LRA_mult of Q.t * 'a
  | LRA_const of Q.t
  | LRA_simplex_var of 'a (* an opaque variable *)
  | LRA_simplex_pred of 'a * S_op.t * Q.t (* an atomic constraint *)
  | LRA_other of 'a

let map_view f (l:_ lra_view) : _ lra_view =
  begin match l with
    | LRA_pred (p, a, b) -> LRA_pred (p, f a, f b)
    | LRA_op (p, a, b) -> LRA_op (p, f a, f b)
    | LRA_mult (n,a) -> LRA_mult (n, f a)
    | LRA_const q -> LRA_const q
    | LRA_simplex_var v -> LRA_simplex_var (f v)
    | LRA_simplex_pred (v, op, q) -> LRA_simplex_pred (f v, op, q)
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

  val mk_and : S.T.Term.state -> term -> term -> term
  val mk_or : S.T.Term.state -> term -> term -> term

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
    : Linear_expr.VAR
      with type t = A.term
       and type lit = Tag.t
  = struct
    type t = A.term
    let pp = A.S.T.Term.pp
    let compare = A.S.T.Term.compare
    type lit = Tag.t
    let pp_lit = Tag.pp
  end

  module LE_ = Linear_expr.Make(struct include Q let pp=pp_print end)(SimpVar)
  module LE = LE_.Expr
  module SimpSolver = Simplex2.Make(SimpVar)
  module LConstr = SimpSolver.Constraint

  type state = {
    tst: T.state;
    simps: T.t T.Tbl.t; (* cache *)
    gensym: A.Gensym.t;
    neq_encoded: unit T.Tbl.t;
    (* if [a != b] asserted and not in this table, add clause [a = b \/ a<b \/ a>b] *)
    needs_th_combination: LE_.Comb.t T.Tbl.t; (* terms that require theory combination *)
    t_defs: LE.t T.Tbl.t; (* term definitions *)
    pred_defs: (pred * LE.t * LE.t * T.t * T.t) T.Tbl.t; (* predicate definitions *)
    local_eqs: (N.t * N.t) Backtrack_stack.t; (* inferred by the congruence closure *)
    simplex: SimpSolver.t;
  }
  (* TODO *)

  let create tst : state =
    { tst;
      simps=T.Tbl.create 128;
      gensym=A.Gensym.create tst;
      neq_encoded=T.Tbl.create 16;
      needs_th_combination=T.Tbl.create 8;
      t_defs=T.Tbl.create 8;
      pred_defs=T.Tbl.create 16;
      local_eqs = Backtrack_stack.create();
      simplex=SimpSolver.create ();
    }

  let push_level self =
    SimpSolver.push_level self.simplex;
    Backtrack_stack.push_level self.local_eqs;
    ()

  let pop_levels self n =
    SimpSolver.pop_levels self.simplex n;
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
    | LRA_pred _ | LRA_simplex_pred _ ->
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
    | LRA_simplex_var v -> LE.monomial1 v
    | LRA_const q -> LE.of_const q

  let as_linexp_id = as_linexp ~f:CCFun.id

  (* TODO: keep the linexps until they're asserted;
     TODO: but use simplification in preprocess
     *)

  (* preprocess linear expressions away *)
  let preproc_lra (self:state) si ~recurse ~mk_lit ~add_clause (t:T.t) : T.t option =
    Log.debugf 50 (fun k->k "lra.preprocess %a" T.pp t);
    let tst = SI.tst si in

    let mk_eq x q =
      let t1 = A.mk_lra tst (LRA_simplex_pred (x, Leq, q)) in
      let t2 = A.mk_lra tst (LRA_simplex_pred (x, Geq, q)) in
      A.mk_and tst t1 t2
    and mk_neq x q =
      let t1 = A.mk_lra tst (LRA_simplex_pred (x, Lt, q)) in
      let t2 = A.mk_lra tst (LRA_simplex_pred (x, Gt, q)) in
      A.mk_or tst t1 t2
    in

    match A.view_as_lra t with
    | LRA_pred (pred, t1, t2) ->
      let l1 = as_linexp ~f:recurse t1 in
      let l2 = as_linexp ~f:recurse t2 in
      let le = LE.(l1 - l2) in
      let le_comb, le_const = LE.comb le, LE.const le in
      let le_const = Q.neg le_const in
      (* now we have [le_comb <pred> le_const] *)

      begin match LE_.Comb.as_singleton le_comb, pred with
        | None, _ ->
          (* non trivial linexp, give it a fresh name in the simplex *)
          let proxy = fresh_term self ~pre:"_le" (T.ty t1) in
          T.Tbl.replace self.needs_th_combination proxy le_comb;

          let le_comb = LE_.Comb.to_list le_comb in
          List.iter (fun (_,v) -> SimpSolver.add_var self.simplex v) le_comb;
          SimpSolver.define self.simplex proxy le_comb;

          let new_t =
            match pred with
            | Eq -> mk_eq proxy le_const
            | Neq -> mk_neq proxy le_const
            | Leq -> A.mk_lra tst (LRA_simplex_pred (proxy, S_op.Leq, le_const))
            | Lt -> A.mk_lra tst (LRA_simplex_pred (proxy, S_op.Lt, le_const))
            | Geq -> A.mk_lra tst (LRA_simplex_pred (proxy, S_op.Geq, le_const))
            | Gt -> A.mk_lra tst (LRA_simplex_pred (proxy, S_op.Gt, le_const))
          in

          Log.debugf 10 (fun k->k "lra.preprocess@ :%a@ :into %a" T.pp t T.pp new_t);
          Some new_t

        | Some (coeff, v), Eq ->
          let q = Q.(le_const / coeff) in
          Some (mk_eq v q) (* turn into [c.v <= const /\ … >= ..] *)

        | Some (coeff, v), Neq ->
          let q = Q.(le_const / coeff) in
          Some (mk_neq v q) (* turn into [c.v < const \/ … > ..] *)

        | Some (coeff, v), pred ->
          (* [c . v <= const] becomes a direct simplex constraint [v <= const/c] *)
          let q = Q.div le_const coeff in

          let op = match pred with
            | Leq -> S_op.Leq
            | Lt -> S_op.Lt
            | Geq -> S_op.Geq
            | Gt -> S_op.Gt
            | Eq | Neq -> assert false
          in
          (* make sure to swap sides if multiplying with a negative coeff *)
          let op = if Q.(coeff < zero) then S_op.neg_sign op else op in

          let new_t = A.mk_lra tst (LRA_simplex_pred (v, op, q)) in
          Log.debugf 10 (fun k->k "lra.preprocess@ :%a@ :into %a" T.pp t T.pp new_t);
          Some new_t
      end

    | LRA_op _ | LRA_mult _ ->
      let le = as_linexp ~f:recurse t in
      let le_comb, le_const = LE.comb le, LE.const le in
      let le_comb = LE_.Comb.to_list le_comb in
      List.iter (fun (_,v) -> SimpSolver.add_var self.simplex v) le_comb;

      let proxy = fresh_term self ~pre:"_le" (T.ty t) in

      if Q.(le_const = zero) then (
        (* if there is no constant, define [proxy] as [proxy := le_comb] and
           return [proxy] *)
        SimpSolver.define self.simplex proxy le_comb;
        Some proxy
      ) else (
        (* a bit more complicated: we cannot just define [proxy := le_comb]
           because of the coefficient.
           Instead we assert [proxy - le_comb = le_const] using a secondary
           variable [proxy2 := le_comb - proxy]
           and asserting [proxy2 = -le_const] *)
        let proxy2 = fresh_term self ~pre:"_le_diff" (T.ty t) in
        SimpSolver.define self.simplex proxy2
          ((Q.minus_one, proxy) :: le_comb);

        add_clause [
          mk_lit (A.mk_lra tst (LRA_simplex_pred (proxy2, Leq, Q.neg le_const)))
        ];
        add_clause [
          mk_lit (A.mk_lra tst (LRA_simplex_pred (proxy2, Geq, Q.neg le_const)))
        ];

        Some proxy
      )

    | LRA_other t when A.has_ty_real t ->
      let le = LE_.Comb.monomial1 t in
      T.Tbl.replace self.needs_th_combination t le;
      None
    | LRA_const _ | LRA_simplex_pred _ | LRA_simplex_var _ | LRA_other _ -> None

  module Q_map = CCMap.Make(Q)

  (* raise conflict from certificate *)
  let fail_with_cert si acts cert : 'a =
    (* TODO: check certificate *)
    let confl =
      SimpSolver.Unsat_cert.lits cert
      |> CCList.flat_map (Tag.to_lits si)
      |>  List.rev_map SI.Lit.neg
    in
    SI.raise_conflict si acts confl SI.P.default

  let check_simplex_ self si acts : SimpSolver.Subst.t =
    Log.debug 5 "lra: call arith solver";
    let res = Profile.with1 "simplex.solve" SimpSolver.check self.simplex in
    begin match res with
      | SimpSolver.Sat m -> m
      | SimpSolver.Unsat cert ->
        Log.debugf 10
          (fun k->k "(@[lra.check.unsat@ :cert %a@])"
              SimpSolver.Unsat_cert.pp cert);
        fail_with_cert si acts cert
    end

  let partial_check_ self si acts trail : unit =
    Profile.with_ "lra.partial-check" @@ fun () ->
    trail
      (fun lit ->
         let sign = SI.Lit.sign lit in
         let lit_t = SI.Lit.term lit in
         match A.view_as_lra lit_t with
         | LRA_simplex_pred (v, op, q) ->
           let op = if sign then op else S_op.neg_sign op in
           let constr = SimpSolver.Constraint.mk v op q in
           Log.debugf 10
             (fun k->k "(@[lra.partial-check.assert@ %a@])"
                 SimpSolver.Constraint.pp constr);
           begin
             try
               SimpSolver.add_var self.simplex v;
               SimpSolver.add_constraint self.simplex constr (Tag.Lit lit)
             with SimpSolver.E_unsat cert ->
               Log.debugf 10
                 (fun k->k "(@[lra.partial-check.unsat@ :cert %a@])"
                     SimpSolver.Unsat_cert.pp cert);
               fail_with_cert si acts cert
           end
         | _ -> ());

    (* incremental check *)
    ignore (check_simplex_ self si acts : SimpSolver.Subst.t);
    ()

  let final_check_ (self:state) si (acts:SI.actions) (_trail:_ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
    Profile.with_ "lra.final-check" @@ fun () ->
    (* FIXME
    (* add congruence closure equalities *)
    Backtrack_stack.iter self.local_eqs
      ~f:(fun (n1,n2) ->
         let t1 = N.term n1 |> as_linexp_id in
         let t2 = N.term n2 |> as_linexp_id in
         let c = LConstr.eq0 LE.(t1 -  t2) in
         let lit = Tag.CC_eq (n1,n2) in
         SimpSolver.add_constr simplex c lit);
       *)

    Log.debug 5 "lra: call arith solver";
    let model = check_simplex_ self si acts in
    Log.debugf 20 (fun k->k "(@[lra.model@ %a@])" SimpSolver.Subst.pp model);
    Log.debug 5 "lra: solver returns SAT";
    let n_th_comb =
      T.Tbl.keys self.needs_th_combination |> Iter.length
    in
    if n_th_comb > 0 then (
      Log.debugf 5
        (fun k->k "(@[LRA.needs-th-combination@ :n-lits %d@])" n_th_comb);
    );
    Log.debugf 50
      (fun k->k "(@[LRA.needs-th-combination@ :lits %a@])"
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

  let create_and_setup si =
    Log.debug 2 "(th-lra.setup)";
    let st = create (SI.tst si) in
    (* TODO    SI.add_simplifier si (simplify st); *)
    SI.add_preprocess si (preproc_lra st);
    SI.on_final_check si (final_check_ st);
    SI.on_partial_check si (partial_check_ st);
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
