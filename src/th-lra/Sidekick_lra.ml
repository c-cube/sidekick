
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

  (* TODO: remove
  let cnf (self:state) (_si:SI.t) ~mk_lit ~add_clause (t:T.t) : T.t option =
    let rec get_lit (t:T.t) : Lit.t =
      let t_abs, t_sign = T.abs self.tst t in
      let lit =
        match T.Tbl.find self.cnf t_abs with
        | lit -> lit (* cached *)
        | exception Not_found ->
          (* compute and cache *)
          let lit = get_lit_uncached t_abs in
          if not (T.equal (Lit.term lit) t_abs) then (
            T.Tbl.add self.cnf t_abs lit;
          );
          lit
      in
      if t_sign then lit else Lit.neg lit
    and get_lit_uncached t : Lit.t =
      match A.view_as_bool t with
      | B_bool b -> mk_lit (T.bool self.tst b)
      | B_opaque_bool t -> mk_lit t
      | B_not u ->
        let lit = get_lit u in
        Lit.neg lit
      | B_and l ->
        let subs = IArray.to_list_map get_lit l in
        let proxy = fresh_lit ~mk_lit ~pre:"and_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg proxy; u]) subs;
        add_clause (proxy :: List.map Lit.neg subs);
        proxy
      | B_or l ->
        let subs = IArray.to_list_map get_lit l in
        let proxy = fresh_lit ~mk_lit ~pre:"or_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg u; proxy]) subs;
        add_clause (Lit.neg proxy :: subs);
        proxy
      | B_imply (args, u) ->
        let t' =
          or_a self.tst @@
          IArray.append (IArray.map (not_ self.tst) args) (IArray.singleton u) in
        get_lit t'
      | B_ite _ | B_eq _ -> mk_lit t
      | B_equiv (a,b) ->
        let a = get_lit a in
        let b = get_lit b in
        let proxy = fresh_lit ~mk_lit ~pre:"equiv_" self in
        (* proxy => a<=> b,
           ¬proxy => a xor b *)
        add_clause [Lit.neg proxy; Lit.neg a; b];
        add_clause [Lit.neg proxy; Lit.neg b; a];
        add_clause [proxy; a; b];
        add_clause [proxy; Lit.neg a; Lit.neg b];
        proxy
      | B_atom u -> mk_lit u
    in
    let lit = get_lit t in
    let u = Lit.term lit in
    (* put sign back as a "not" *)
    let u = if Lit.sign lit then u else A.mk_bool self.tst (B_not u) in
    if T.equal u t then None else Some u
     *)

  (* check if new terms were added to the congruence closure, that can be turned
     into clauses *)
  let check_new_terms (self:state) si (acts:SI.actions) (_trail:_ Iter.t) : unit =
    let cc_ = SI.cc si in
    let all_terms =
      let open SI in
      CC.all_classes cc_
      |> Iter.flat_map CC.N.iter_class
      |> Iter.map CC.N.term
    in
    let cnf_of t =
      assert false
      (*
      cnf self si t
        ~mk_lit:(SI.mk_lit si acts) ~add_clause:(SI.add_clause_permanent si acts)
    *)
    in
    begin
      all_terms
        (fun t -> match cnf_of t with
           | None -> ()
           | Some u ->
             Log.debugf 5
               (fun k->k "(@[th-lra.final-check.cnf@ %a@ :yields %a@])"
                   T.pp t T.pp u);
             SI.CC.merge_t cc_ t u (SI.CC.Expl.mk_list []);
             ());
    end;
    ()

  let final_check_ (self:state) si (acts:SI.actions) (_trail:_ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
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
