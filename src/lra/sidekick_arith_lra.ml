
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

open Sidekick_core

module Predicate = Sidekick_simplex.Predicate
module Linear_expr = Sidekick_simplex.Linear_expr
module Linear_expr_intf = Sidekick_simplex.Linear_expr_intf

module type INT = Sidekick_arith.INT
module type RATIONAL = Sidekick_arith.RATIONAL

module S_op = Sidekick_simplex.Op

type pred = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq
type op = Linear_expr_intf.op = Plus | Minus

type ('num, 'a) lra_view =
  | LRA_pred of pred * 'a * 'a
  | LRA_op of op * 'a * 'a
  | LRA_mult of 'num * 'a
  | LRA_const of 'num
  | LRA_simplex_var of 'a (* an opaque variable *)
  | LRA_simplex_pred of 'a * S_op.t * 'num (* an atomic constraint *)
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
  module Z : INT
  module Q : RATIONAL with type bigint = Z.t

  type term = S.T.Term.t
  type ty = S.T.Ty.t

  val view_as_lra : term -> (Q.t, term) lra_view
  (** Project the term into the theory view *)

  val mk_bool : S.T.Term.store -> bool -> term

  val mk_lra : S.T.Term.store -> (Q.t, term) lra_view -> term
  (** Make a term from the given theory view *)

  val ty_lra : S.T.Term.store -> ty

  val mk_eq : S.T.Term.store -> term -> term -> term
  (** syntactic equality *)

  val has_ty_real : term -> bool
  (** Does this term have the type [Real] *)

  val lemma_lra : S.Lit.t Iter.t -> S.P.proof_rule

  module Gensym : sig
    type t

    val create : S.T.Term.store -> t

    val tst : t -> S.T.Term.store

    val copy : t -> t

    val fresh_term : t -> pre:string -> S.T.Ty.t -> term
    (** Make a fresh term of the given type *)
  end
end

module type S = sig
  module A : ARG

  (*
  module SimpVar : Sidekick_simplex.VAR with type lit = A.S.Lit.t
  module LE_ : Linear_expr_intf.S with module Var = SimpVar
  module LE = LE_.Expr
     *)

  (** Simplexe *)
  module SimpSolver : Sidekick_simplex.S

  type state

  val create : ?stat:Stat.t ->
    A.S.P.t ->
    A.S.T.Term.store ->
    A.S.T.Ty.store ->
    state

  (* TODO: be able to declare some variables as ints *)

  (*
  val simplex : state -> Simplex.t
     *)

  val k_state : state A.S.Solver_internal.Registry.key
  (** Key to access the state from outside,
      available when the theory has been setup *)

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
      | By_def -> Fmt.string out "by-def"
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
    let not_lit = function
      | Tag.Lit l -> Some (Tag.Lit (Lit.neg l))
      | _ -> None
  end

  module LE_ = Linear_expr.Make(A.Q)(SimpVar)
  module LE = LE_.Expr
  module SimpSolver = Sidekick_simplex.Make(struct
      module Z = A.Z
      module Q = A.Q
      module Var = SimpVar
      let mk_lit _ _ _ = assert false
    end)
  module Subst = SimpSolver.Subst

  module Comb_map = CCMap.Make(LE_.Comb)

  type state = {
    tst: T.store;
    ty_st: Ty.store;
    proof: SI.P.t;
    simps: T.t T.Tbl.t; (* cache *)
    gensym: A.Gensym.t;
    in_model: unit T.Tbl.t; (* terms to add to model *)
    encoded_eqs: unit T.Tbl.t; (* [a=b] gets clause [a = b <=> (a >= b /\ a <= b)] *)
    needs_th_combination: unit T.Tbl.t; (* terms that require theory combination *)
    mutable encoded_le: T.t Comb_map.t; (* [le] -> var encoding [le] *)
    local_eqs: (N.t * N.t) Backtrack_stack.t; (* inferred by the congruence closure *)
    simplex: SimpSolver.t;
    mutable last_res: SimpSolver.result option;
    stat_th_comb: int Stat.counter;
  }

  let create ?(stat=Stat.create()) proof tst ty_st : state =
    { tst; ty_st;
      proof;
      in_model=T.Tbl.create 8;
      simps=T.Tbl.create 128;
      gensym=A.Gensym.create tst;
      encoded_eqs=T.Tbl.create 8;
      needs_th_combination=T.Tbl.create 8;
      encoded_le=Comb_map.empty;
      local_eqs = Backtrack_stack.create();
      simplex=SimpSolver.create ~stat ();
      last_res=None;
      stat_th_comb=Stat.mk_int stat "lra.th-comb";
    }

  let[@inline] reset_res_ (self:state) : unit =
    self.last_res <- None

  let push_level self =
    SimpSolver.push_level self.simplex;
    Backtrack_stack.push_level self.local_eqs;
    ()

  let pop_levels self n =
    reset_res_ self;
    SimpSolver.pop_levels self.simplex n;
    Backtrack_stack.pop_levels self.local_eqs n ~f:(fun _ -> ());
    ()

  let fresh_term self ~pre ty = A.Gensym.fresh_term self.gensym ~pre ty
  let fresh_lit (self:state) ~mk_lit ~pre : Lit.t =
    let t = fresh_term ~pre self (Ty.bool self.ty_st) in
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

  (* return a variable that is equal to [le_comb] in the simplex. *)
  let var_encoding_comb ~pre self (le_comb:LE_.Comb.t) : T.t =
    match LE_.Comb.as_singleton le_comb with
    | Some (c, x) when A.Q.(c = one) -> x (* trivial linexp *)
    | _ ->
      match Comb_map.find le_comb self.encoded_le with
      | x -> x (* already encoded that *)
      | exception Not_found ->
        (* new variable to represent [le_comb] *)
        let proxy = fresh_term self ~pre (A.ty_lra self.tst) in
        (* TODO: define proxy *)
        self.encoded_le <- Comb_map.add le_comb proxy self.encoded_le;
        Log.debugf 50
          (fun k->k "(@[lra.encode-linexp@ `%a`@ :into-var %a@])" LE_.Comb.pp le_comb T.pp proxy);

        (* it's actually 0 *)
        if LE_.Comb.is_empty le_comb then (
          Log.debug 50 "(lra.encode-linexp.is-trivially-0)";
          SimpSolver.add_constraint self.simplex
            ~on_propagate:(fun _ ~reason:_ -> ())
            (SimpSolver.Constraint.leq proxy A.Q.zero) Tag.By_def;
          SimpSolver.add_constraint self.simplex
            ~on_propagate:(fun _ ~reason:_ -> ())
            (SimpSolver.Constraint.geq proxy A.Q.zero) Tag.By_def;
        ) else (
          LE_.Comb.iter (fun v _ -> SimpSolver.add_var self.simplex v) le_comb;
          SimpSolver.define self.simplex proxy (LE_.Comb.to_list le_comb);
        );
        proxy

  let add_clause_lra_ ?using (module PA:SI.PREPROCESS_ACTS) lits =
    let pr = A.lemma_lra (Iter.of_list lits) PA.proof in
    let pr = match using with
      | None -> pr
      | Some using -> SI.P.lemma_rw_clause pr ~res:(Iter.of_list lits) ~using PA.proof in
    PA.add_clause lits pr

  (* preprocess linear expressions away *)
  let preproc_lra (self:state) si (module PA:SI.PREPROCESS_ACTS)
      (t:T.t) : (T.t * SI.proof_step Iter.t) option =
    Log.debugf 50 (fun k->k "(@[lra.preprocess@ %a@])" T.pp t);
    let tst = SI.tst si in

    (* preprocess subterm *)
    let preproc_t ~steps t =
      let u, pr = SI.preprocess_term si (module PA) t in
      T.Tbl.replace self.in_model t ();
      CCOpt.iter (fun s -> steps := s :: !steps) pr;
      u
    in

    (* tell the CC this term exists *)
    let declare_term_to_cc t =
      Log.debugf 50 (fun k->k "(@[simplex2.declare-term-to-cc@ %a@])" T.pp t);
      ignore (SI.CC.add_term (SI.cc si) t : SI.CC.N.t);
    in

    match A.view_as_lra t with
    | LRA_pred ((Eq | Neq), t1, t2) ->
      (* the equality side. *)
      let t, _ = T.abs tst t in
      if not (T.Tbl.mem self.encoded_eqs t) then (
        let u1 = A.mk_lra tst (LRA_pred (Leq, t1, t2)) in
        let u2 = A.mk_lra tst (LRA_pred (Geq, t1, t2)) in

        T.Tbl.add self.encoded_eqs t ();

        (* encode [t <=> (u1 /\ u2)] *)
        let lit_t = PA.mk_lit_nopreproc t in
        let lit_u1 = PA.mk_lit_nopreproc u1 in
        let lit_u2 = PA.mk_lit_nopreproc u2 in
        add_clause_lra_ (module PA) [SI.Lit.neg lit_t; lit_u1];
        add_clause_lra_ (module PA) [SI.Lit.neg lit_t; lit_u2];
        add_clause_lra_ (module PA)
          [SI.Lit.neg lit_u1; SI.Lit.neg lit_u2; lit_t];
      );
      None

    | LRA_pred (pred, t1, t2) ->
      let steps = ref [] in
      let l1 = as_linexp ~f:(preproc_t ~steps) t1 in
      let l2 = as_linexp ~f:(preproc_t ~steps) t2 in
      let le = LE.(l1 - l2) in
      let le_comb, le_const = LE.comb le, LE.const le in
      let le_const = A.Q.neg le_const in
      (* now we have [le_comb <pred> le_const] *)

      begin match LE_.Comb.as_singleton le_comb, pred with
        | None, _ ->
          (* non trivial linexp, give it a fresh name in the simplex *)
          let proxy = var_encoding_comb self ~pre:"_le" le_comb in
          let pr_def = SI.P.define_term proxy t PA.proof in
          steps := pr_def :: !steps;
          declare_term_to_cc proxy;

          let op =
            match pred with
            | Eq | Neq -> assert false (* unreachable *)
            | Leq -> S_op.Leq
            | Lt -> S_op.Lt
            | Geq -> S_op.Geq
            | Gt -> S_op.Gt
          in

          let new_t = A.mk_lra tst (LRA_simplex_pred (proxy, op, le_const)) in
          begin
            let lit = PA.mk_lit_nopreproc new_t in
            let constr = SimpSolver.Constraint.mk proxy op le_const in
            SimpSolver.declare_bound self.simplex constr (Tag.Lit lit);
          end;

          Log.debugf 10 (fun k->k "(@[lra.preprocess:@ %a@ :into %a@])" T.pp t T.pp new_t);
          Some (new_t, Iter.of_list !steps)

        | Some (coeff, v), pred ->
          (* [c . v <= const] becomes a direct simplex constraint [v <= const/c] *)
          let q = A.Q.( le_const / coeff ) in
          declare_term_to_cc v;

          let op = match pred with
            | Leq -> S_op.Leq
            | Lt -> S_op.Lt
            | Geq -> S_op.Geq
            | Gt -> S_op.Gt
            | Eq | Neq -> assert false
          in
          (* make sure to swap sides if multiplying with a negative coeff *)
          let op = if A.Q.(coeff < zero) then S_op.neg_sign op else op in

          let new_t = A.mk_lra tst (LRA_simplex_pred (v, op, q)) in
          begin
            let lit = PA.mk_lit_nopreproc new_t in
            let constr = SimpSolver.Constraint.mk v op q in
            SimpSolver.declare_bound self.simplex constr (Tag.Lit lit);
          end;

          Log.debugf 10 (fun k->k "lra.preprocess@ :%a@ :into %a" T.pp t T.pp new_t);
          Some (new_t, Iter.of_list !steps)
      end

    | LRA_op _ | LRA_mult _ ->
      let steps = ref [] in
      let le = as_linexp ~f:(preproc_t ~steps) t in
      let le_comb, le_const = LE.comb le, LE.const le in

      if A.Q.(le_const = zero) then (
        (* if there is no constant, define [proxy] as [proxy := le_comb] and
           return [proxy] *)
        let proxy = var_encoding_comb self ~pre:"_le" le_comb in
        begin
          let pr_def = SI.P.define_term proxy t PA.proof in
          steps := pr_def :: !steps;
        end;
        declare_term_to_cc proxy;

        Some (proxy, Iter.of_list !steps)
      ) else (
        (* a bit more complicated: we cannot just define [proxy := le_comb]
           because of the coefficient.
           Instead we assert [proxy - le_comb = le_const] using a secondary
           variable [proxy2 := le_comb - proxy]
           and asserting [proxy2 = -le_const] *)
        let proxy = fresh_term self ~pre:"_le" (T.ty t) in
        begin
          let pr_def = SI.P.define_term proxy t PA.proof in
          steps := pr_def :: !steps;
        end;
        let proxy2 = fresh_term self ~pre:"_le_diff" (T.ty t) in
        let pr_def2 =
          SI.P.define_term proxy (A.mk_lra tst (LRA_op (Minus, t, proxy))) PA.proof
        in

        SimpSolver.add_var self.simplex proxy;
        LE_.Comb.iter (fun v _ -> SimpSolver.add_var self.simplex v) le_comb;

        SimpSolver.define self.simplex proxy2
          ((A.Q.minus_one, proxy) :: LE_.Comb.to_list le_comb);

        Log.debugf 50
          (fun k->k "(@[lra.encode-linexp.with-offset@ %a@ :var %a@ :diff-var %a@])"
              LE_.Comb.pp le_comb T.pp proxy T.pp proxy2);

        declare_term_to_cc proxy;
        declare_term_to_cc proxy2;

        add_clause_lra_ ~using:Iter.(return pr_def2) (module PA) [
          PA.mk_lit_nopreproc (A.mk_lra tst (LRA_simplex_pred (proxy2, Leq, A.Q.neg le_const)))
        ];
        add_clause_lra_ ~using:Iter.(return pr_def2) (module PA) [
          PA.mk_lit_nopreproc (A.mk_lra tst (LRA_simplex_pred (proxy2, Geq, A.Q.neg le_const)))
        ];

        Some (proxy, Iter.of_list !steps)
      )

    | LRA_other t when A.has_ty_real t -> None
    | LRA_const _ | LRA_simplex_pred _ | LRA_simplex_var _ | LRA_other _ ->
      None

  let simplify (self:state) (_recurse:_) (t:T.t) : (T.t * SI.proof_step Iter.t) option =

    let proof_eq t u =
      A.lemma_lra
        (Iter.return (SI.Lit.atom self.tst (A.mk_eq self.tst t u))) self.proof
    in
    let proof_bool t ~sign:b =
      let lit = SI.Lit.atom ~sign:b self.tst t in
      A.lemma_lra (Iter.return lit) self.proof
    in

    match A.view_as_lra t with
    | LRA_op _ | LRA_mult _ ->
      let le = as_linexp_id t in
      if LE.is_const le then (
        let c = LE.const le in
        let u = A.mk_lra self.tst (LRA_const c) in
        let pr = proof_eq t u in
        Some (u, Iter.return pr)
      ) else None
    | LRA_pred (pred, l1, l2) ->
      let le = LE.(as_linexp_id l1 - as_linexp_id l2) in
      if LE.is_const le then (
        let c = LE.const le in
        let is_true = match pred with
          | Leq -> A.Q.(c <= zero)
          | Geq -> A.Q.(c >= zero)
          | Lt -> A.Q.(c < zero)
          | Gt -> A.Q.(c > zero)
          | Eq -> A.Q.(c = zero)
          | Neq -> A.Q.(c <> zero)
        in
        let u = A.mk_bool self.tst is_true in
        let pr = proof_bool t ~sign:is_true in
        Some (u, Iter.return pr)
      ) else None
    | _ -> None

  module Q_map = CCMap.Make(A.Q)

  (* raise conflict from certificate *)
  let fail_with_cert si acts cert : 'a =
    Profile.with1 "lra.simplex.check-cert" SimpSolver._check_cert cert;
    let confl =
      SimpSolver.Unsat_cert.lits cert
      |> CCList.flat_map (Tag.to_lits si)
      |>  List.rev_map SI.Lit.neg
    in
    let pr = A.lemma_lra (Iter.of_list confl) (SI.proof si) in
    SI.raise_conflict si acts confl pr

  let on_propagate_ si acts lit ~reason =
    match lit with
    | Tag.Lit lit ->
      (* TODO: more detailed proof certificate *)
      SI.propagate si acts lit
        ~reason:(fun() ->
           let lits = CCList.flat_map (Tag.to_lits si) reason in
           let pr = A.lemma_lra Iter.(cons lit (of_list lits)) (SI.proof si) in
           CCList.flat_map (Tag.to_lits si) reason, pr)
    | _ -> ()

  let check_simplex_ self si acts : SimpSolver.Subst.t =
    Log.debug 5 "(lra.check-simplex)";
    let res =
      Profile.with_ "lra.simplex.solve"
        (fun () ->
           SimpSolver.check self.simplex
             ~on_propagate:(on_propagate_ si acts))
    in
    self.last_res <- Some res;
    begin match res with
      | SimpSolver.Sat m -> m
      | SimpSolver.Unsat cert ->
        Log.debugf 10
          (fun k->k "(@[lra.check.unsat@ :cert %a@])"
              SimpSolver.Unsat_cert.pp cert);
        fail_with_cert si acts cert
    end

  (* TODO: trivial propagations *)

  let add_local_eq (self:state) si acts n1 n2 : unit =
    Log.debugf 20 (fun k->k "(@[lra.add-local-eq@ %a@ %a@])" N.pp n1 N.pp n2);
    reset_res_ self;
    let t1 = N.term n1 in
    let t2 = N.term n2 in
    let t1, t2 = if T.compare t1 t2 > 0 then t2, t1 else t1, t2 in

    let le = LE.(as_linexp_id t1 - as_linexp_id t2) in
    let le_comb, le_const = LE.comb le, LE.const le in
    let le_const = A.Q.neg le_const in

    let v = var_encoding_comb ~pre:"le_local_eq" self le_comb in
    let lit = Tag.CC_eq (n1,n2) in
    begin
      try
        let c1 = SimpSolver.Constraint.geq v le_const in
        SimpSolver.add_constraint self.simplex c1 lit
          ~on_propagate:(on_propagate_ si acts);
        let c2 = SimpSolver.Constraint.leq v le_const in
        SimpSolver.add_constraint self.simplex c2 lit
          ~on_propagate:(on_propagate_ si acts);
      with SimpSolver.E_unsat cert ->
        fail_with_cert si acts cert
    end;
    ()

  (* theory combination: add decisions [t=u] whenever [t] and [u]
     have the same value in [subst] and both occur under function symbols *)
  let do_th_combination (self:state) si acts (subst:Subst.t) : unit =
    Log.debug 5 "(lra.do-th-combinations)";
    let n_th_comb = T.Tbl.keys self.needs_th_combination |> Iter.length in
    if n_th_comb > 0 then (
      Log.debugf 5
        (fun k->k "(@[lra.needs-th-combination@ :n-lits %d@])" n_th_comb);
      Log.debugf 50
        (fun k->k "(@[lra.needs-th-combination@ :terms [@[%a@]]@])"
            (Util.pp_iter @@ Fmt.within "`" "`" T.pp) (T.Tbl.keys self.needs_th_combination));
    );

    (* theory combination: for [t1,t2] terms in [self.needs_th_combination]
       that have same value, but are not provably equal, push
       decision [t1=t2] into the SAT solver. *)
    begin
      let by_val: T.t list Q_map.t =
        T.Tbl.keys self.needs_th_combination
        |> Iter.map (fun t -> Subst.eval subst t, t)
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
                          A.Q.pp _q T.pp t1 T.pp t2);
                    assert(SI.cc_mem_term si t1);
                    assert(SI.cc_mem_term si t2);
                    (* if both [t1] and [t2] are relevant to the congruence
                       closure, and are not equal in it yet, add [t1=t2] as
                       the next decision to do *)
                    if not (SI.cc_are_equal si t1 t2) then (
                      Log.debug 50 "LRA.th-comb.must-decide-equal";
                      Stat.incr self.stat_th_comb;
                      Profile.instant "lra.th-comb-assert-eq";

                      let t = A.mk_eq (SI.tst si) t1 t2 in
                      let lit = SI.mk_lit si acts t in
                      SI.push_decision si acts lit
                    )
                 )
           end)
        by_val;
      ()
    end;
    ()

  (* partial checks is where we add literals from the trail to the
     simplex. *)
  let partial_check_ self si acts trail : unit =
    Profile.with_ "lra.partial-check" @@ fun () ->

    reset_res_ self;
    let changed = ref false in
    trail
      (fun lit ->
         let sign = SI.Lit.sign lit in
         let lit_t = SI.Lit.term lit in
         Log.debugf 50 (fun k->k "(@[lra.partial-check.add@ :lit %a@ :lit-t %a@])"
                           SI.Lit.pp lit T.pp lit_t);
         match A.view_as_lra lit_t with
         | LRA_simplex_pred (v, op, q) ->

           (* need to account for the literal's sign *)
           let op = if sign then op else S_op.not_ op in

           (* assert new constraint to Simplex *)
           let constr = SimpSolver.Constraint.mk v op q in
           Log.debugf 10
             (fun k->k "(@[lra.partial-check.assert@ %a@])"
                 SimpSolver.Constraint.pp constr);
           begin
             changed := true;
             try
               SimpSolver.add_var self.simplex v;
               SimpSolver.add_constraint self.simplex constr (Tag.Lit lit)
                 ~on_propagate:(on_propagate_ si acts);
             with SimpSolver.E_unsat cert ->
               Log.debugf 10
                 (fun k->k "(@[lra.partial-check.unsat@ :cert %a@])"
                     SimpSolver.Unsat_cert.pp cert);
               fail_with_cert si acts cert
           end
         | _ -> ());

    (* incremental check *)
    if !changed then (
      ignore (check_simplex_ self si acts : SimpSolver.Subst.t);
    );
    ()

  let final_check_ (self:state) si (acts:SI.theory_actions) (_trail:_ Iter.t) : unit =
    Log.debug 5 "(th-lra.final-check)";
    Profile.with_ "lra.final-check" @@ fun () ->
    reset_res_ self;

    (* add congruence closure equalities *)
    Backtrack_stack.iter self.local_eqs
      ~f:(fun (n1,n2) -> add_local_eq self si acts n1 n2);

    (* TODO: jiggle model to reduce the number of variables that
       have the same value *)
    let model = check_simplex_ self si acts in
    Log.debugf 20 (fun k->k "(@[lra.model@ %a@])" SimpSolver.Subst.pp model);
    Log.debug 5 "(lra: solver returns SAT)";
    do_th_combination self si acts model;
    ()

  (* look for subterms of type Real, for they will need theory combination *)
  let on_subterm (self:state) _ (t:T.t) : unit =
    Log.debugf 50 (fun k->k "(@[lra.cc-on-subterm@ %a@])" T.pp t);
    match A.view_as_lra t with
    | LRA_other _ when not (A.has_ty_real t) -> ()
    | _ ->
      if not (T.Tbl.mem self.needs_th_combination t) then (
        Log.debugf 5 (fun k->k "(@[lra.needs-th-combination@ %a@])" T.pp t);
        T.Tbl.add self.needs_th_combination t ()
      )

  let to_rat_t_ self q = A.mk_lra self.tst (LRA_const q)

  (* help generating model *)
  let model_gen_ (self:state) ~recurse:_ _si n : _ option =
    let t = N.term n in
    begin match self.last_res with
      | Some (SimpSolver.Sat m) ->
        Log.debugf 50 (fun k->k "lra: model ask %a" T.pp t);
        SimpSolver.V_map.get t m |> CCOpt.map (to_rat_t_ self)
      | _ -> None
    end

  (* help generating model *)
  let model_complete_ (self:state) _si ~add : unit =
    Log.debugf 30 (fun k->k "lra: model complete");
    begin match self.last_res with
      | Some (SimpSolver.Sat m) when T.Tbl.length self.in_model > 0 ->
        Log.debugf 50 (fun k->k "(@[lra.in_model@ %a@])"
                          (Util.pp_iter T.pp) (T.Tbl.keys self.in_model));

        let add_t t () =
          match SimpSolver.V_map.get t m with
          | None -> ()
          | Some u -> add t (to_rat_t_ self u)
        in
        T.Tbl.iter add_t self.in_model

      | _ -> ()
    end

  let k_state = SI.Registry.create_key ()

  let create_and_setup si =
    Log.debug 2 "(th-lra.setup)";
    let stat = SI.stats si in
    let st = create ~stat (SI.proof si) (SI.tst si) (SI.ty_st si) in
    SI.Registry.set (SI.registry si) k_state st;
    SI.add_simplifier si (simplify st);
    SI.on_preprocess si (preproc_lra st);
    SI.on_final_check si (final_check_ st);
    SI.on_partial_check si (partial_check_ st);
    SI.on_model si ~ask:(model_gen_ st) ~complete:(model_complete_ st);
    SI.on_cc_is_subterm si (on_subterm st);
    SI.on_cc_post_merge si
      (fun _ _ n1 n2 ->
         if A.has_ty_real (N.term n1) then (
           Backtrack_stack.push st.local_eqs (n1, n2)
         ));
    st

  let theory =
    A.S.mk_theory
      ~name:"th-lra"
      ~create_and_setup ~push_level ~pop_levels
      ()
end
