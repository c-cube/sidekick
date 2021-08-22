(** Core of the SMT solver using Sidekick_sat

    Sidekick_sat (in src/sat/) is a modular SAT solver in
    pure OCaml.

    This builds a {!Sidekick_core.SOLVER} on top of it.
*)

(** Argument to pass to the functor {!Make} in order to create a
    new Msat-based SMT solver. *)
module type ARG = sig
  open Sidekick_core
  module T : TERM
  module Lit : LIT with module T = T
  type proof
  module P : PROOF
    with type term = T.Term.t
     and type t = proof
     and type lit = Lit.t

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t

  val is_valid_literal : T.Term.t -> bool
  (** Is this a valid boolean literal? (e.g. is it a closed term, not inside
      a quantifier) *)
end

module type S = Sidekick_core.SOLVER

(** Main functor to get a solver. *)
module Make(A : ARG)
  : S
    with module T = A.T
     and type proof = A.proof
     and module Lit = A.Lit
     and module P = A.P
= struct
  module T = A.T
  module P = A.P
  module Ty = T.Ty
  module Term = T.Term
  module Lit = A.Lit
  type term = Term.t
  type ty = Ty.t
  type proof = A.proof
  type dproof = proof -> unit
  type lit = Lit.t

  (* actions from the sat solver *)
  type sat_acts = (lit, proof) Sidekick_sat.acts

  (* the full argument to the congruence closure *)
  module CC_actions = struct
    module T = T
    module P = P
    module Lit = Lit
    type nonrec proof = proof
    let cc_view = A.cc_view

    module Actions = struct
      module T = T
      module P = P
      module Lit = Lit
      type nonrec proof = proof
      type dproof = proof -> unit
      type t = sat_acts
      let[@inline] raise_conflict (a:t) lits (dp:dproof) =
        let (module A) = a in
        A.raise_conflict lits dp
      let[@inline] propagate (a:t) lit ~reason =
        let (module A) = a in
        let reason = Sidekick_sat.Consequence reason in
        A.propagate lit reason
    end
  end

  module CC = Sidekick_cc.Make(CC_actions)
  module Expl = CC.Expl
  module N = CC.N

  (** Internal solver, given to theories and to Msat *)
  module Solver_internal = struct
    module T = T
    module P = P
    module Lit = Lit
    module CC = CC
    module N = CC.N
    type formula = Lit.t
    type nonrec proof = proof
    type dproof = proof -> unit
    type term = Term.t
    type ty = Ty.t
    type lit = Lit.t
    type term_store = Term.store
    type ty_store = Ty.store

    type th_states =
      | Ths_nil
      | Ths_cons : {
          st: 'a;
          push_level: 'a -> unit;
          pop_levels: 'a -> int -> unit;
          next: th_states;
        } -> th_states

    type theory_actions = sat_acts

    module Simplify = struct
      type t = {
        tst: term_store;
        ty_st: ty_store;
        proof: proof;
        mutable hooks: hook list;
        cache: Term.t Term.Tbl.t;
      }
      and hook = t -> term -> term option

      let create tst ty_st ~proof : t =
        {tst; ty_st; proof; hooks=[]; cache=Term.Tbl.create 32;}

      let[@inline] tst self = self.tst
      let[@inline] ty_st self = self.ty_st
      let[@inline] with_proof self f = P.with_proof self.proof f
      let add_hook self f = self.hooks <- f :: self.hooks
      let clear self = Term.Tbl.clear self.cache

      let normalize (self:t) (t:Term.t) : Term.t option =
        (* compute and cache normal form of [t] *)
        let rec aux t : Term.t =
          match Term.Tbl.find self.cache t with
          | u -> u
          | exception Not_found ->
            let u = aux_rec t self.hooks in
            Term.Tbl.add self.cache t u;
            u
        (* try each function in [hooks] successively, and rewrite subterms *)
        and aux_rec t hooks = match hooks with
          | [] ->
            let u = Term.map_shallow self.tst aux t in
            if Term.equal t u then t else aux u
          | h :: hooks_tl ->
            match h self t with
            | None -> aux_rec t hooks_tl
            | Some u when Term.equal t u -> aux_rec t hooks_tl
            | Some u -> aux u (* fixpoint *)
        in
        let u = aux t in
        if Term.equal t u then None
        else (
          (* proof: [sub_proofs |- t=u] by CC + subproof *)
          P.with_proof self.proof (P.lemma_preprocess t u);
          Some u
        )

      let normalize_t self t =
        match normalize self t with
        | Some u -> u
        | None -> t
    end
    type simplify_hook = Simplify.hook

    module type PREPROCESS_ACTS = sig
      val mk_lit : ?sign:bool -> term -> lit
      val add_clause : lit list -> dproof -> unit
      val add_lit : ?default_pol:bool -> lit -> unit
    end
    type preprocess_actions = (module PREPROCESS_ACTS)

    type t = {
      tst: Term.store; (** state for managing terms *)
      ty_st: Ty.store;
      cc: CC.t lazy_t; (** congruence closure *)
      proof: proof; (** proof logger *)
      stat: Stat.t;
      count_axiom: int Stat.counter;
      count_preprocess_clause: int Stat.counter;
      count_conflict: int Stat.counter;
      count_propagate: int Stat.counter;
      mutable on_progress: unit -> unit;
      simp: Simplify.t;
      mutable preprocess: preprocess_hook list;
      mutable mk_model: model_hook list;
      preprocess_cache: Term.t Term.Tbl.t;
      mutable t_defs : (term*term) list; (* term definitions *)
      mutable th_states : th_states; (** Set of theories *)
      mutable on_partial_check: (t -> theory_actions -> lit Iter.t -> unit) list;
      mutable on_final_check: (t -> theory_actions -> lit Iter.t -> unit) list;
      mutable level: int;
    }

    and preprocess_hook =
      t ->
      preprocess_actions ->
      term -> term option

    and model_hook =
      recurse:(t -> CC.N.t -> term) ->
      t -> CC.N.t -> term option

    type solver = t

    module Eq_class = CC.N
    module Expl = CC.Expl
    module Proof = P

    let[@inline] cc (t:t) = Lazy.force t.cc
    let[@inline] tst t = t.tst
    let[@inline] ty_st t = t.ty_st
    let[@inline] with_proof self f = Proof.with_proof self.proof f
    let stats t = t.stat

    let define_const (self:t) ~const ~rhs : unit =
      self.t_defs <- (const,rhs) :: self.t_defs

    let simplifier self = self.simp
    let simplify_t self (t:Term.t) : _ option = Simplify.normalize self.simp t
    let simp_t self (t:Term.t) : Term.t = Simplify.normalize_t self.simp t

    let add_simplifier (self:t) f : unit = Simplify.add_hook self.simp f

    let on_preprocess self f = self.preprocess <- f :: self.preprocess
    let on_model_gen self f = self.mk_model <- f :: self.mk_model

    let push_decision (_self:t) (acts:theory_actions) (lit:lit) : unit =
      let (module A) = acts in
      let sign = Lit.sign lit in
      A.add_decision_lit (Lit.abs lit) sign

    let[@inline] raise_conflict self (acts:theory_actions) c proof : 'a =
      let (module A) = acts in
      Stat.incr self.count_conflict;
      A.raise_conflict c proof

    let[@inline] propagate self (acts:theory_actions) p ~reason : unit =
      let (module A) = acts in
      Stat.incr self.count_propagate;
      A.propagate p (Sidekick_sat.Consequence reason)

    let[@inline] propagate_l self acts p cs proof : unit =
      propagate self acts p ~reason:(fun()->cs,proof)

    let add_sat_clause_ self (acts:theory_actions) ~keep lits (proof:dproof) : unit =
      let (module A) = acts in
      Stat.incr self.count_axiom;
      A.add_clause ~keep lits proof

    let add_sat_lit self ?default_pol (acts:theory_actions) (lit:Lit.t) : unit =
      let (module A) = acts in
      A.add_lit ?default_pol lit

    (* actual preprocessing logic, acting on terms.
       this calls all the preprocessing hooks on subterms, ensuring
       a fixpoint. *)
    let preprocess_term_ (self:t) (module A0:PREPROCESS_ACTS) (t:term) : term =
      let mk_lit_nopreproc t = Lit.atom self.tst t in (* no further simplification *)

      (* compute and cache normal form [u] of [t].

         Also cache a list of proofs [ps] such that [ps |- t=u] by CC.
         It is important that we cache the proofs here, because
         next time we preprocess [t], we will have to re-emit the same
         proofs, even though we will not do any actual preprocessing work.
      *)
      let rec preproc_rec t : term =
        match Term.Tbl.find self.preprocess_cache t with
        | u -> u
        | exception Not_found ->
          (* try rewrite at root *)
          let t1 = preproc_with_hooks t self.preprocess in

          (* map subterms *)
          let t2 = Term.map_shallow self.tst preproc_rec t1 in

          let u =
            if not (Term.equal t t2) then (
              preproc_rec t2 (* fixpoint *)
            ) else (
              t2
            )
          in

          (* signal boolean subterms, so as to decide them
             in the SAT solver *)
          if Ty.is_bool (Term.ty u) then (
            Log.debugf 5
              (fun k->k "(@[solver.map-bool-subterm-to-lit@ :subterm %a@])" Term.pp u);

            (* make a literal (already preprocessed) *)
            let lit = mk_lit_nopreproc u in
            (* ensure that SAT solver has a boolean atom for [u] *)
            A0.add_lit lit;

            (* also map [sub] to this atom in the congruence closure, for propagation *)
            let cc = cc self in
            CC.set_as_lit cc (CC.add_term cc u) lit;
          );

          if t != u then (
            Log.debugf 5
              (fun k->k "(@[smt-solver.preprocess.term@ :from %a@ :to %a@])"
                  Term.pp t Term.pp u);
          );

          Term.Tbl.add self.preprocess_cache t u;
          u

      (* try each function in [hooks] successively *)
      and preproc_with_hooks t hooks : term =
        match hooks with
        | [] -> t
        | h :: hooks_tl ->
          (* call hook, using [pacts] which will ensure all new
             literals and clauses are also preprocessed *)
          match h self (Lazy.force pacts) t with
          | None -> preproc_with_hooks t hooks_tl
          | Some u -> preproc_rec u

      (* create literal and preprocess it with [pacts], which uses [A0]
         for the base operations, and preprocesses new literals and clauses
         recursively. *)
      and mk_lit ?sign t =
        let u = preproc_rec t in
        if not (Term.equal t u) then (
          Log.debugf 10
            (fun k->k "(@[smt-solver.preprocess.t@ :t %a@ :into %a@])"
                Term.pp t Term.pp u);
        );
        Lit.atom self.tst ?sign u

      and preprocess_lit (lit:lit) : lit =
        let t = Lit.term lit in
        let sign = Lit.sign lit in
        mk_lit ~sign t

      (* wrap [A0] so that all operations go throught preprocessing *)
      and pacts = lazy (
        (module struct
          let add_lit ?default_pol lit =
            let lit = preprocess_lit lit in
            A0.add_lit lit
          let add_clause c pr =
            Stat.incr self.count_preprocess_clause;
            let c = CCList.map preprocess_lit c in
            A0.add_clause c pr
          let mk_lit = mk_lit
        end : PREPROCESS_ACTS)
      ) in

      P.begin_subproof self.proof;

      (* simplify the term *)
      let t1 = simp_t self t in

      (* preprocess *)
      let u = preproc_rec t1 in
      (* emit [|- t=u] *)
      if not (Term.equal t u) then (
        P.with_proof self.proof (P.lemma_preprocess t u);
      );

      P.end_subproof self.proof;
      u

    (* return preprocessed lit *)
    let preprocess_lit_ (self:t) (pacts:preprocess_actions) (lit:lit) : lit =
      let t = Lit.term lit in
      let sign = Lit.sign lit in
      let u = preprocess_term_ self pacts t in
      Lit.atom self.tst ~sign u

    (* add a clause using [acts] *)
    let add_clause_ self acts lits (proof:dproof) : unit =
      add_sat_clause_ self acts ~keep:true lits proof

    let[@inline] add_lit _self (acts:theory_actions) ?default_pol lit : unit =
      let (module A) = acts in
      A.add_lit ?default_pol lit

    let preprocess_acts_of_acts (self:t) (acts:theory_actions) : preprocess_actions =
      (module struct
        let mk_lit ?sign t = Lit.atom self.tst ?sign t
        let add_clause = add_clause_ self acts
        let add_lit = add_lit self acts
      end)

    let preprocess_clause_ (self:t) (acts:theory_actions) (c:lit list) : lit list =
      let pacts = preprocess_acts_of_acts self acts in
      let c = CCList.map (preprocess_lit_ self pacts) c in
      c

    (* make literal and preprocess it *)
    let[@inline] mk_plit (self:t) (pacts:preprocess_actions) ?sign (t:term) : lit =
      let lit = Lit.atom self.tst ?sign t in
      preprocess_lit_ self pacts lit

    let[@inline] preprocess_term self (pacts:preprocess_actions) (t:term) : term =
      preprocess_term_ self pacts t

    let[@inline] add_clause_temp self acts c (proof:dproof) : unit =
      let c = preprocess_clause_ self acts c in
      add_sat_clause_ self acts ~keep:false c proof

    let[@inline] add_clause_permanent self acts c (proof:dproof) : unit =
      let c = preprocess_clause_ self acts c in
      add_sat_clause_ self acts ~keep:true c proof

    let[@inline] mk_lit (self:t) (acts:theory_actions) ?sign t : lit =
      let pacts = preprocess_acts_of_acts self acts in
      mk_plit self pacts ?sign t

    let add_lit_t self acts ?sign t =
      let pacts = preprocess_acts_of_acts self acts in
      let lit = mk_plit self pacts ?sign t in
      add_lit self acts lit

    let on_final_check self f = self.on_final_check <- f :: self.on_final_check
    let on_partial_check self f = self.on_partial_check <- f :: self.on_partial_check
    let on_cc_new_term self f = CC.on_new_term (cc self) f
    let on_cc_pre_merge self f = CC.on_pre_merge (cc self) f
    let on_cc_post_merge self f = CC.on_post_merge (cc self) f
    let on_cc_conflict self f = CC.on_conflict (cc self) f
    let on_cc_propagate self f = CC.on_propagate (cc self) f
    let on_cc_is_subterm self f = CC.on_is_subterm (cc self) f

    let cc_add_term self t = CC.add_term (cc self) t
    let cc_mem_term self t = CC.mem_term (cc self) t
    let cc_find self n = CC.find (cc self) n
    let cc_are_equal self t1 t2 =
      let n1 = cc_add_term self t1 in
      let n2 = cc_add_term self t2 in
      N.equal (cc_find self n1) (cc_find self n2)
    let cc_merge self _acts n1 n2 e = CC.merge (cc self) n1 n2 e
    let cc_merge_t self acts t1 t2 e =
      cc_merge self acts (cc_add_term self t1) (cc_add_term self t2) e
    let cc_raise_conflict_expl self acts e =
      CC.raise_conflict_from_expl (cc self) acts e

    (** {2 Interface with the SAT solver} *)

    let rec push_lvl_ = function
      | Ths_nil -> ()
      | Ths_cons r -> r.push_level r.st; push_lvl_ r.next

    let rec pop_lvls_ n = function
      | Ths_nil -> ()
      | Ths_cons r -> r.pop_levels r.st n; pop_lvls_ n r.next

    let push_level (self:t) : unit =
      self.level <- 1 + self.level;
      CC.push_level (cc self);
      push_lvl_ self.th_states

    let pop_levels (self:t) n : unit =
      self.level <- self.level - n;
      CC.pop_levels (cc self) n;
      pop_lvls_ n self.th_states

    exception E_loop_exit

    (* handle a literal assumed by the SAT solver *)
    let assert_lits_ ~final (self:t) (acts:theory_actions) (lits:Lit.t Iter.t) : unit =
      Log.debugf 2
        (fun k->k "(@[<hv1>@{<green>smt-solver.assume_lits@}%s[lvl=%d]@ %a@])"
            (if final then "[final]" else "") self.level (Util.pp_iter ~sep:"; " Lit.pp) lits);
      (* transmit to CC *)
      let cc = cc self in
      if not final then (
        CC.assert_lits cc lits;
      );
      (* transmit to theories. *)
      CC.check cc acts;
      if final then (
        try
          while true do
            (* TODO: theory combination *)
            List.iter (fun f -> f self acts lits) self.on_final_check;
            CC.check cc acts;
            if not @@ CC.new_merges cc then (
              raise_notrace E_loop_exit
            );
          done;
        with E_loop_exit ->
          ()
      ) else (
        List.iter (fun f -> f self acts lits) self.on_partial_check;
      );
      ()

    let[@inline] iter_atoms_ (acts:theory_actions) : _ Iter.t =
      fun f ->
        let (module A) = acts in
        A.iter_assumptions f

    (* propagation from the bool solver *)
    let check_ ~final (self:t) (acts: sat_acts) =
      let pb = if final then Profile.begin_ "solver.final-check" else Profile.null_probe in
      let iter = iter_atoms_ acts in
      Log.debugf 5 (fun k->k "(smt-solver.assume :len %d)" (Iter.length iter));
      self.on_progress();
      assert_lits_ ~final self acts iter;
      Profile.exit pb

    (* propagation from the bool solver *)
    let[@inline] partial_check (self:t) (acts:_ Sidekick_sat.acts) : unit =
      check_ ~final:false self acts

    (* perform final check of the model *)
    let[@inline] final_check (self:t) (acts:_ Sidekick_sat.acts) : unit =
      check_ ~final:true self acts

    let create ~stat ~proof (tst:Term.store) (ty_st:Ty.store) () : t =
      let rec self = {
        tst;
        ty_st;
        cc = lazy (
          (* lazily tie the knot *)
          CC.create ~size:`Big self.tst;
        );
        proof;
        th_states=Ths_nil;
        stat;
        simp=Simplify.create tst ty_st ~proof;
        on_progress=(fun () -> ());
        preprocess=[];
        mk_model=[];
        preprocess_cache=Term.Tbl.create 32;
        count_axiom = Stat.mk_int stat "solver.th-axioms";
        count_preprocess_clause = Stat.mk_int stat "solver.preprocess-clause";
        count_propagate = Stat.mk_int stat "solver.th-propagations";
        count_conflict = Stat.mk_int stat "solver.th-conflicts";
        t_defs=[];
        on_partial_check=[];
        on_final_check=[];
        level=0;
      } in
      ignore (Lazy.force @@ self.cc : CC.t);
      self
  end

  (** the parametrized SAT Solver *)
  module Sat_solver = Sidekick_sat.Make_cdcl_t(Solver_internal)

  (* main solver state *)
  type t = {
    si: Solver_internal.t;
    solver: Sat_solver.t;
    stat: Stat.t;
    proof: P.t;
    count_clause: int Stat.counter;
    count_solve: int Stat.counter;
    (* config: Config.t *)
  }
  type solver = t

  module type THEORY = sig
    type t
    val name : string
    val create_and_setup : Solver_internal.t -> t
    val push_level : t -> unit
    val pop_levels : t -> int -> unit
  end

  type theory = (module THEORY)
  type 'a theory_p = (module THEORY with type t = 'a)

  (** {2 Main} *)

  let add_theory_p (type a) (self:t) (th:a theory_p) : a =
    let (module Th) = th in
    Log.debugf 2
      (fun k-> k "(@[smt-solver.add-theory@ :name %S@])" Th.name);
    let st = Th.create_and_setup self.si in
    (* add push/pop to the internal solver *)
    begin
      let open Solver_internal in
      self.si.th_states <- Ths_cons {
          st;
          push_level=Th.push_level;
          pop_levels=Th.pop_levels;
          next=self.si.th_states;
        };
    end;
    st

  let add_theory (self:t) (th:theory) : unit =
    let (module Th) = th in
    ignore (add_theory_p self (module Th))

  let add_theory_l self = List.iter (add_theory self)

  (* create a new solver *)
  let create ?(stat=Stat.global) ?size ~proof ~theories tst ty_st () : t =
    Log.debug 5 "smt-solver.create";
    let si = Solver_internal.create ~stat ~proof tst ty_st () in
    let self = {
      si; proof;
      solver=Sat_solver.create ~proof ?size si;
      stat;
      count_clause=Stat.mk_int stat "solver.add-clause";
      count_solve=Stat.mk_int stat "solver.solve";
    } in
    add_theory_l self theories;
    (* assert [true] and [not false] *)
    begin
      let tst = Solver_internal.tst self.si in
      let t_true = Term.bool tst true in
      Sat_solver.add_clause self.solver
        [Lit.atom tst t_true]
        (P.lemma_true t_true)
    end;
    self

  let[@inline] solver self = self.solver
  let[@inline] cc self = Solver_internal.cc self.si
  let[@inline] stats self = self.stat
  let[@inline] tst self = Solver_internal.tst self.si
  let[@inline] ty_st self = Solver_internal.ty_st self.si

  let preprocess_acts_of_solver_
      (self:t) : (module Solver_internal.PREPROCESS_ACTS) =
    (module struct
      let mk_lit ?sign t = Lit.atom ?sign self.si.tst t
      let add_lit ?default_pol lit =
        Sat_solver.add_lit self.solver ?default_pol lit
      let add_clause c pr =
        Sat_solver.add_clause self.solver c pr
    end)

  (* preprocess literal *)
  let preprocess_lit_ (self:t) (lit:lit) : lit =
    let pacts = preprocess_acts_of_solver_ self in
    Solver_internal.preprocess_lit_ self.si pacts lit

  (* make a literal from a term, ensuring it is properly preprocessed *)
  let mk_lit_t (self:t) ?sign (t:term) : lit =
    let pacts = preprocess_acts_of_solver_ self in
    Solver_internal.mk_plit self.si pacts ?sign t

  (** {2 Result} *)

  module Unknown = struct
    type t =
      | U_timeout
      | U_max_depth
      | U_incomplete

    let pp out = function
      | U_timeout -> Fmt.string out "timeout"
      | U_max_depth -> Fmt.string out "max depth reached"
      | U_incomplete -> Fmt.string out "incomplete fragment"
  end [@@ocaml.warning "-37"]

  module Model = struct
    type t =
      | Empty
      | Map of term Term.Tbl.t
    let empty = Empty
    let mem = function
      | Empty -> fun _ -> false
      | Map tbl -> Term.Tbl.mem tbl
    let find = function
      | Empty -> fun _ -> None
      | Map tbl -> Term.Tbl.get tbl
    let eval = find
    let pp out = function
      | Empty -> Fmt.string out "(model)"
      | Map tbl ->
        let pp_pair out (t,v) =
          Fmt.fprintf out "(@[<1>%a@ := %a@])" Term.pp t Term.pp v
            in
        Fmt.fprintf out "(@[<hv>model@ %a@])"
          (Util.pp_iter pp_pair) (Term.Tbl.to_iter tbl)
  end

  type res =
    | Sat of Model.t
    | Unsat of {
        unsat_core: unit -> lit Iter.t;
      }
    | Unknown of Unknown.t
    (** Result of solving for the current set of clauses *)

  (** {2 Main} *)

  let pp_stats out (self:t) : unit =
    Stat.pp_all out (Stat.all @@ stats self)

  let add_clause (self:t) (c:lit IArray.t) (proof:dproof) : unit =
    Stat.incr self.count_clause;
    Log.debugf 50 (fun k->
        k "(@[solver.add-clause@ %a@])"
          (Util.pp_iarray Lit.pp) c);
    let pb = Profile.begin_ "add-clause" in
    Sat_solver.add_clause_a self.solver (c:> lit array) proof;
    Profile.exit pb

  let add_clause_l self c p = add_clause self (IArray.of_list c) p

  let assert_terms self c =
    let c = CCList.map (fun t -> Lit.atom (tst self) t) c in
    let c = CCList.map (preprocess_lit_ self) c in
    (* TODO: if c != c0 then P.emit_redundant_clause c
       because we jsut preprocessed it away? *)
    let dp = P.emit_input_clause (Iter.of_list c) in
    add_clause_l self c dp

  let assert_term self t = assert_terms self [t]

  let mk_model (self:t) (lits:lit Iter.t) : Model.t =
    Log.debug 1 "(smt.solver.mk-model)";
    Profile.with_ "smt-solver.mk-model" @@ fun () ->
    let module M = Term.Tbl in
    let model = M.create 128 in
    let {Solver_internal.tst; cc=lazy cc; mk_model=model_hooks; _} = self.si in

    (* first, add all literals to the model using the given propositional model
       [lits]. *)
    lits
      (fun lit ->
         let t, sign = Lit.signed_term lit in
         M.replace model t (Term.bool tst sign));

    (* compute a value for [n]. *)
    let rec val_for_class (n:N.t) : term =
      let repr = CC.find cc n in

      (* see if a value is found already (always the case if it's a boolean) *)
      match M.get model (N.term repr) with
      | Some t_val -> t_val
      | None ->

        (* try each model hook *)
        let rec aux = function
          | [] -> N.term repr
          | h :: hooks ->
            begin match h ~recurse:(fun _ n -> val_for_class n) self.si repr with
              | None -> aux hooks
              | Some t -> t
            end
        in

        let t_val = aux model_hooks in
        M.replace model (N.term repr) t_val; (* be sure to cache the value *)
        t_val
    in

    (* map terms of each CC class to the value computed for their class. *)
    Solver_internal.CC.all_classes (Solver_internal.cc self.si)
      (fun repr ->
         let t_val = val_for_class repr in (* value for this class *)
         N.iter_class repr
           (fun u ->
              let t_u = N.term u in
              if not (N.equal u repr) && not (Term.equal t_u t_val) then (
                M.replace model t_u t_val;
              )));
    Model.Map model

  let solve ?(on_exit=[]) ?(check=true) ?(on_progress=fun _ -> ())
      ~assumptions (self:t) : res =
    Profile.with_ "smt-solver.solve" @@ fun () ->
    let do_on_exit () =
      List.iter (fun f->f()) on_exit;
    in
    self.si.on_progress <- (fun () -> on_progress self);

    let r = Sat_solver.solve ~assumptions (solver self) in
    Stat.incr self.count_solve;
    match r with
    | Sat_solver.Sat (module SAT) ->
      Log.debug 1 "sidekick.smt-solver: SAT";
      let _lits f = SAT.iter_trail f in
      (* TODO: theory combination *)
      let m = mk_model self _lits in
      do_on_exit ();
      Sat m
    | Sat_solver.Unsat (module UNSAT) ->
      let unsat_core () = UNSAT.unsat_assumptions () in
      do_on_exit ();
      Unsat {unsat_core}

  let mk_theory (type st)
      ~name ~create_and_setup
      ?(push_level=fun _ -> ()) ?(pop_levels=fun _ _ -> ())
      () : theory =
    let module Th = struct
      type t = st
      let name = name
      let create_and_setup = create_and_setup
      let push_level = push_level
      let pop_levels = pop_levels
    end in
    (module Th : THEORY)
end
