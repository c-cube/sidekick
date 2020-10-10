
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

open Sidekick_core

type pred = Lt | Leq | Eq | Neq | Geq | Gt
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

(* TODO: upstream *)
let neg_pred = function
  | Leq -> Gt
  | Lt -> Geq
  | Eq -> Neq
  | Neq -> Eq
  | Geq -> Lt
  | Gt -> Leq

let pred_to_funarith = function
  | Leq -> `Leq
  | Lt -> `Lt
  | Geq -> `Geq
  | Gt -> `Gt
  | Eq -> `Eq
  | Neq -> `Neq


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

  type simp_var =
    | V_fresh of int
    | V_t of T.t

  (** Simplex variables *)
  module Simp_vars = struct
    type t = simp_var
    let compare a b =
      match a, b with
      | V_fresh i, V_fresh j -> CCInt.compare i j
      | V_fresh _, V_t _ -> -1
      | V_t _, V_fresh _ -> 1
      | V_t t1, V_t t2 -> T.compare t1 t2
    let pp out = function
      | V_fresh i -> Fmt.fprintf out "$fresh_%d" i
      | V_t t -> T.pp out t
    module Fresh = struct
      type t = int ref
      let create() : t = ref 0
      let fresh n = V_fresh (CCRef.get_then_incr n)
    end
  end

  module Simplex = Funarith_zarith.Simplex.Make_full(Simp_vars)
  module LE = Simplex.L.Expr
  module LComb = Simplex.L.Comb
  module Constr = Simplex.L.Constr

  type state = {
    tst: T.state;
    simps: T.t T.Tbl.t; (* cache *)
    simplex: Simplex.t;
    gensym: A.Gensym.t;
    mutable t_defs: (T.t * LE.t) list; (* term definitions *)
    pred_defs: (pred * LE.t * LE.t) T.Tbl.t; (* predicate definitions *)
  }

  let create tst : state =
    { tst; simps=T.Tbl.create 128;
      gensym=A.Gensym.create tst;
      simplex=Simplex.create();
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
    | LRA_other _ -> LE.of_list Q.zero [Q.one, V_t t]
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
    | LRA_const q -> LE.of_const q

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

  let final_check_ (self:state) _si (_acts:SI.actions) (trail:_ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
    let simplex = Simplex.create() in
    (* first, add definitions *)
    begin
      List.iter
        (fun (t,le) ->
           let open LE.Infix in
           let c =
             Constr.of_expr (le - LE.of_comb (LComb.monomial1 (V_t t))) `Eq
           in
           Simplex.add_constr simplex c)
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
               let open LE.Infix in
               let e = a - b in
               let pred = if sign then pred else neg_pred pred in
               let pred = match pred_to_funarith pred with
                 | `Neq -> Sidekick_util.Error.errorf "cannot handle negative LEQ equality"
                 | (`Eq | `Geq | `Gt | `Leq | `Lt) as p -> p
               in
               let c = Constr.of_expr e pred in
               Simplex.add_constr simplex c;
           end)
    end;
    Log.debug 5 "lra: call simplex";
    begin match Simplex.solve simplex with
      | Simplex.Solution _ ->
        Log.debug 5 "lra: simplex returns SAT";
        () (* TODO: model combination *)
      | Simplex.Unsatisfiable cert ->
        Log.debugf 5 (fun k->k"lra: simplex returns UNSAT@ with cert %a" Simplex.pp_cert cert);
        (* find what terms are involved *)
        let asserts =
          cert.Simplex.cert_expr
          |> Iter.of_list
          |> Iter.filter_map
            (function
              | V_t -> Some t
              | V_fresh _ -> None)
          |> Iter.to_rev_list
        in
        Simplex.cert
        () (* TODO: produce conflict *)
    end;
    ()

  let create_and_setup si =
    Log.debug 2 "(th-lra.setup)";
    let st = create (SI.tst si) in
    (* TODO    SI.add_simplifier si (simplify st); *)
    SI.add_preprocess si (preproc_lra st);
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
