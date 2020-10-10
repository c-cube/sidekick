
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

open Sidekick_core

module FM = Fourier_motzkin

type pred = FM.Pred.t = Lt | Leq | Geq | Gt | Neq | Eq
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

  val view_as_lra : term -> term lra_view
  (** Project the term into the theory view *)

  val mk_lra : S.T.Term.state -> term lra_view -> term
  (** Make a term from the given theory view *)

  module Gensym : sig
    type t

    val create : S.T.Term.state -> t

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

  (* the fourier motzkin module *)
  module FM_A = FM.Make(struct
      module T = T
      type tag = Lit.t
    end)

  (* linear expressions *)
  module LE = FM_A.LE

  type state = {
    tst: T.state;
    simps: T.t T.Tbl.t; (* cache *)
    gensym: A.Gensym.t;
    neq_encoded: unit T.Tbl.t;
    (* if [a != b] asserted and not in this table, add clause [a = b \/ a<b \/ a>b] *)
    mutable t_defs: (T.t * LE.t) list; (* term definitions *)
    pred_defs: (pred * LE.t * LE.t) T.Tbl.t; (* predicate definitions *)
  }

  let create tst : state =
    { tst;
      simps=T.Tbl.create 128;
      gensym=A.Gensym.create tst;
      neq_encoded=T.Tbl.create 16;
      t_defs=[];
      pred_defs=T.Tbl.create 16;
    }

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

  (* turn the term into a linear expression *)
  let rec as_linexp (t:T.t) : LE.t =
    let open LE.Infix in
    match A.view_as_lra t with
    | LRA_other _ -> LE.var t
    | LRA_pred _ ->
      Error.errorf "type error: in linexp, LRA predicate %a" T.pp t
    | LRA_op (op, t1, t2) ->
      let t1 = as_linexp t1 in
      let t2 = as_linexp t2 in
      begin match op with
        | Plus -> t1 + t2
        | Minus -> t1 - t2
      end
    | LRA_mult (n, x) ->
      let t = as_linexp x in
      LE.( n * t )
    | LRA_const q -> LE.const q

  (* TODO: keep the linexps until they're asserted;
     TODO: but use simplification in preprocess
     *)

  (* preprocess linear expressions away *)
  let preproc_lra self si ~mk_lit:_ ~add_clause:_ (t:T.t) : T.t option =
    Log.debugf 50 (fun k->k "lra.preprocess %a" T.pp t);
    let _tst = SI.tst si in
    match A.view_as_lra t with
    | LRA_pred (pred, t1, t2) ->
      (* TODO: map preproc on [l1] and [l2] *)
      let l1 = as_linexp t1 in
      let l2 = as_linexp t2 in
      let proxy = fresh_term self ~pre:"_pred_lra_" Ty.bool in
      T.Tbl.add self.pred_defs proxy (pred, l1, l2);
      Log.debugf 5 (fun k->k"lra.preprocess.step %a :into %a" T.pp t T.pp proxy);
      Some proxy
    | LRA_op _ | LRA_mult _ ->
      let le = as_linexp t in
      (* TODO: map preproc on [le] *)
      let proxy = fresh_term self ~pre:"_e_lra_" (T.ty t) in
      self.t_defs <- (proxy, le) :: self.t_defs;
      Log.debugf 5 (fun k->k"lra.preprocess.step %a :into %a" T.pp t T.pp proxy);
      Some proxy
    | LRA_const _ | LRA_other _ -> None

  (* partial check: just ensure [a != b] triggers the clause
     [a=b \/ a<b \/ a>b] *)
  let partial_check_ (self:state) si (acts:SI.actions) (trail:_ Iter.t) : unit =
    let tst = self.tst in
    begin
      trail
      |> Iter.filter (fun lit -> not (Lit.sign lit))
      |> Iter.filter_map
        (fun lit ->
           let t = Lit.term lit in
           match A.view_as_lra t with
           | LRA_pred (Eq, a, b) when not (T.Tbl.mem self.neq_encoded t) ->
             Some (lit, a,b)
           | _ -> None)
      |> Iter.iter
        (fun (lit,a,b) ->
           let c = [
             Lit.abs lit;
             SI.mk_lit si acts (A.mk_lra tst (LRA_pred (Lt, a, b)));
             SI.mk_lit si acts (A.mk_lra tst (LRA_pred (Lt, b, a)));
           ] in
           SI.add_clause_permanent si acts c;
           T.Tbl.add self.neq_encoded (Lit.term lit) ();
        )
    end

  let final_check_ (self:state) si (acts:SI.actions) (trail:_ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
    let fm = FM_A.create() in
    (* first, add definitions *)
    begin
      List.iter
        (fun (t,le) ->
           let open LE.Infix in
           let le = le - LE.var t in
           let c = FM_A.Constr.mk ?tag:None Eq (LE.var t) le in
           FM_A.assert_c fm c)
        self.t_defs
    end;
    (* add trail *)
    begin
      trail
      |> Iter.iter
        (fun lit ->
           let sign = Lit.sign lit in
           let t = Lit.term lit in
           begin match T.Tbl.find self.pred_defs t with
             | exception Not_found -> ()
             | (pred, a, b) ->
               let pred = if sign then pred else FM.Pred.neg pred in
               if pred = Neq then (
                 Log.debugf 50 (fun k->k "skip neq in %a" T.pp t);
               ) else (
                 let c = FM_A.Constr.mk ~tag:lit pred a b in
                 FM_A.assert_c fm c;
               )
           end)
    end;
    Log.debug 5 "lra: call arith solver";
    begin match FM_A.solve fm with
      | FM_A.Sat ->
        Log.debug 5 "lra: solver returns SAT";
        () (* TODO: get a model + model combination *)
      | FM_A.Unsat lits ->
        (* we tagged assertions with their lit, so the certificate being an
           unsat core translates directly into a conflict clause *)
        Log.debugf 5 (fun k->k"lra: solver returns UNSAT@ with cert %a"
                         (Fmt.Dump.list Lit.pp) lits);
        let confl = List.rev_map Lit.neg lits in
        (* TODO: produce and store a proper LRA resolution proof *)
        SI.raise_conflict si acts confl SI.P.default
    end;
    ()

  let create_and_setup si =
    Log.debug 2 "(th-lra.setup)";
    let st = create (SI.tst si) in
    (* TODO    SI.add_simplifier si (simplify st); *)
    SI.add_preprocess si (preproc_lra st);
    SI.on_partial_check si (partial_check_ st);
    SI.on_final_check si (final_check_ st);
    (*     SI.add_preprocess si (cnf st); *)
    (* TODO: theory combination *)
    st

  let theory =
    A.S.mk_theory
      ~name:"th-lra"
      ~create_and_setup
      ()
end
