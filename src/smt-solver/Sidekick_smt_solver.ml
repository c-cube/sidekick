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

    type actions = sat_acts

    module Simplify = struct
      type t = {
        tst: term_store;
        ty_st: ty_store;
        mutable hooks: hook list;
        cache: Term.t Term.Tbl.t;
      }
      and hook = t -> term -> (term * dproof) option

      let create tst ty_st : t =
        {tst; ty_st; hooks=[]; cache=Term.Tbl.create 32;}
      let[@inline] tst self = self.tst
      let[@inline] ty_st self = self.ty_st
      let add_hook self f = self.hooks <- f :: self.hooks
      let clear self = Term.Tbl.clear self.cache

      let normalize (self:t) (t:Term.t) : (Term.t * dproof) option =
        let sub_proofs_: dproof list ref = ref [] in

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
            | Some (u, _) when Term.equal t u -> aux_rec t hooks_tl
            | Some (u, pr_t_u) ->
              sub_proofs_ := pr_t_u :: !sub_proofs_;
              aux u
        in
        let u = aux t in
        if Term.equal t u then None
        else (
          (* proof: [sub_proofs |- t=u] by CC + subproof *)
          let emit_proof p =
            if not (T.Term.equal t u) then (
              P.begin_subproof p;
              List.iter (fun dp -> dp p) !sub_proofs_;
              P.lemma_preprocess p t u;
              P.end_subproof p;
            )
          in
          Some (u, emit_proof)
        )

      let normalize_t self t =
        match normalize self t with
        | Some (u,pr) -> u, pr
        | None -> t, (fun _ -> ())
    end
    type simplify_hook = Simplify.hook

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
      preprocess_cache: (Term.t * dproof list) Term.Tbl.t;
      mutable t_defs : (term*term) list; (* term definitions *)
      mutable th_states : th_states; (** Set of theories *)
      mutable on_partial_check: (t -> actions -> lit Iter.t -> unit) list;
      mutable on_final_check: (t -> actions -> lit Iter.t -> unit) list;
      mutable level: int;
    }

    and preprocess_hook =
      t ->
      mk_lit:(term -> lit) ->
      add_clause:(lit list -> dproof -> unit) ->
      term -> (term * dproof) option

    and model_hook =
      recurse:(t -> CC.N.t -> term) ->
      t -> CC.N.t -> term option

    type solver = t

    module Formula = struct
      include Lit
      let norm lit =
        let lit', sign = Lit.norm_sign lit in
        lit', if sign then Sidekick_sat.Same_sign else Sidekick_sat.Negated
    end
    module Eq_class = CC.N
    module Expl = CC.Expl
    module Proof = P

    let[@inline] cc (t:t) = Lazy.force t.cc
    let[@inline] tst t = t.tst
    let[@inline] ty_st t = t.ty_st
    let stats t = t.stat

    let define_const (self:t) ~const ~rhs : unit =
      self.t_defs <- (const,rhs) :: self.t_defs

    let simplifier self = self.simp
    let simplify_t self (t:Term.t) : _ option = Simplify.normalize self.simp t
    let simp_t self (t:Term.t) : Term.t * dproof = Simplify.normalize_t self.simp t

    let add_simplifier (self:t) f : unit = Simplify.add_hook self.simp f

    let on_preprocess self f = self.preprocess <- f :: self.preprocess
    let on_model_gen self f = self.mk_model <- f :: self.mk_model

    let push_decision (_self:t) (acts:actions) (lit:lit) : unit =
      let (module A) = acts in
      let sign = Lit.sign lit in
      A.add_decision_lit (Lit.abs lit) sign

    let[@inline] raise_conflict self (acts:actions) c proof : 'a =
      let (module A) = acts in
      Stat.incr self.count_conflict;
      A.raise_conflict c proof

    let[@inline] propagate self (acts:actions) p ~reason : unit =
      let (module A) = acts in
      Stat.incr self.count_propagate;
      A.propagate p (Sidekick_sat.Consequence reason)

    let[@inline] propagate_l self acts p cs proof : unit =
      propagate self acts p ~reason:(fun()->cs,proof)

    let add_sat_clause_ self (acts:actions) ~keep lits (proof:dproof) : unit =
      let (module A) = acts in
      Stat.incr self.count_axiom;
      A.add_clause ~keep lits proof

    let preprocess_term_ (self:t) ~add_clause (t:term) : term * dproof =
      let mk_lit t = Lit.atom self.tst t in (* no further simplification *)

      (* compute and cache normal form [u] of [t].
         Also cache a list of proofs [ps] such
         that [ps |- t=u] by CC. *)
      let rec aux t : term * dproof list =
        match Term.Tbl.find self.preprocess_cache t with
        | u, ps ->
          u, ps
        | exception Not_found ->
          let sub_p: _ list ref = ref [] in

          (* try rewrite at root *)
          let t1 = aux_rec ~sub_p t self.preprocess in

          (* map subterms *)
          let t2 =
            Term.map_shallow self.tst
              (fun t_sub ->
                 let u_sub, ps_t = aux t_sub in
                 if not (Term.equal t_sub u_sub) then (
                   sub_p := List.rev_append ps_t !sub_p;
                 );
                 u_sub)
              t1
          in

          let u =
            if not (Term.equal t t2) then (
              (* fixpoint *)
              let v, ps_t2_v = aux t2 in
              if not (Term.equal t2 v) then (
                sub_p := List.rev_append ps_t2_v !sub_p
              );
              v
            ) else (
              t2
            )
          in

          if t != u then (
            Log.debugf 5
              (fun k->k "(@[smt-solver.preprocess.term@ :from %a@ :to %a@])"
                  Term.pp t Term.pp u);
          );

          Term.Tbl.add self.preprocess_cache t (u,!sub_p);
          u, !sub_p

      (* try each function in [hooks] successively *)
      and aux_rec ~sub_p t hooks : term =
        match hooks with
        | [] -> t
        | h :: hooks_tl ->
          match h self ~mk_lit ~add_clause t with
          | None -> aux_rec ~sub_p t hooks_tl
          | Some (u, ps_t_u) ->
            sub_p := ps_t_u :: !sub_p;
            let v, ps_u_v = aux u in
            if t != v then (
              sub_p := List.rev_append ps_u_v !sub_p;
            );
            v
      in

      let t1, p_t_t1 = simp_t self t in

      let u, ps_t1_u = aux t1 in

      let emit_proof_t_eq_u =
        if t != u then (
          let hyps =
            if t == t1 then ps_t1_u
            else p_t_t1 :: ps_t1_u in
          let emit_proof p =
            P.begin_subproof p;
            List.iter (fun dp -> dp p) hyps;
            P.lemma_preprocess p t u;
            P.end_subproof p;
          in
          emit_proof
        ) else (fun _->())
      in

      u, emit_proof_t_eq_u

    (* return preprocessed lit + proof they are equal *)
    let preprocess_lit_ (self:t) ~add_clause (lit:lit) : lit * dproof =
      let t, p = Lit.term lit |> preprocess_term_ self ~add_clause in
      let lit' = Lit.atom self.tst ~sign:(Lit.sign lit) t in

      if not (Lit.equal lit lit') then (
        Log.debugf 10
          (fun k->k "(@[smt-solver.preprocess.lit@ :lit %a@ :into %a@])"
              Lit.pp lit Lit.pp lit');
      );

      lit', p

    (* add a clause using [acts] *)
    let add_clause_ self acts lits (proof:dproof) : unit =
      Stat.incr self.count_preprocess_clause;
      add_sat_clause_ self acts ~keep:true lits proof

    (* FIXME: should we store the proof somewhere? *)
    let mk_lit self acts ?sign t : Lit.t =
      let add_clause = add_clause_ self acts in
      let lit, _p =
        preprocess_lit_ self ~add_clause @@ Lit.atom self.tst ?sign t
      in
      lit

    let[@inline] preprocess_term self ~add_clause (t:term) : term * dproof =
      preprocess_term_ self ~add_clause t

    let[@inline] add_clause_temp self acts lits (proof:dproof) : unit =
      add_sat_clause_ self acts ~keep:false lits proof

    let[@inline] add_clause_permanent self acts lits (proof:dproof) : unit =
      add_sat_clause_ self acts ~keep:true lits proof

    let[@inline] add_lit _self (acts:actions) lit : unit =
      let (module A) = acts in
      A.mk_lit lit

    let add_lit_t self acts ?sign t =
      let lit = mk_lit self acts ?sign t in
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
    let assert_lits_ ~final (self:t) (acts:actions) (lits:Lit.t Iter.t) : unit =
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

    let[@inline] iter_atoms_ (acts:actions) : _ Iter.t =
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
        simp=Simplify.create tst ty_st;
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

  (* TODO: move somewhere else? where it can be used to implement the new
     proof module?
  module Pre_proof = struct
    module SP = Sat_solver.Proof
    module SC = Sat_solver.Clause

    type t = {
      solver: Sat_solver.t;
      msat: Sat_solver.Proof.t;
      tdefs: (term*term) list; (* term definitions *)
      p: P.t lazy_t;
    }

    let to_proof (self:t) : P.t = Lazy.force self.p

    let pp_dot =
      let module Dot =
        Sidekick_backend.Dot.Make(Sat_solver)(Sidekick_backend.Dot.Default(Sat_solver)) in
      let pp out self = Dot.pp (Sat_solver.store self.solver) out self.msat in
      Some pp

    (* export to proof {!P.t}, translating Msat-level proof ising:
       - [stepc name cl proof] to bind [name] to given clause and proof
       - [deft name t] to define [name] as a shortcut for [t] (tseitin, etc.).
         Checker will always expand these. (TODO)
       - [steps <defc>+] for a structure proof with definitions, returning last one
       - [subproof (assms <lit>* ) (proof)] which uses [proof] to get
         clause [c] under given assumptions (each assm is a lit),
         and return [-a1 \/ … \/ -an \/ c], discharging assumptions
    *)
    let conv_proof (store:Sat_solver.store) (msat:Sat_solver.Proof.t) (t_defs:_ list) : P.t =
      let assms = ref [] in
      let steps = ref [] in

      let n_step = ref 0 in
      let n_tbl_: string SC.Tbl.t = SC.Tbl.create 32 in (* node.concl -> unique idx *)

      (* name of an already processed proof node *)
      let find_proof_name (p:Sat_solver.Proof.t) : string =
        try SC.Tbl.find n_tbl_ (SP.conclusion p)
        with Not_found ->
          Error.errorf
            "msat-solver.pre-proof.to_proof: cannot find proof step with conclusion %a"
            (SC.pp store) (SP.conclusion p)
      in

      let add_step s = steps := s :: !steps in

      (* convert [n_init] into a proof step and adds it to [steps] *)
      let tr_node_to_step () (n_init:SP.proof_node) : unit =
        let {SP.conclusion=c; step} = n_init in

        if SC.Tbl.mem n_tbl_ c then ()
        else (
          let name = Printf.sprintf "c%d" !n_step in
          incr n_step;

          SC.Tbl.add n_tbl_ c name;

          (* build conclusion of proof step *)
          let tr_atom a : P.lit =
            let sign = Sat_solver.Atom.sign a in
            let t = Lit.term (Sat_solver.Atom.formula store a) in
            P.lit_mk sign t
          in
          let concl = List.rev_map tr_atom @@ Sat_solver.Clause.atoms_l store c in

          (* proof for the node *)
          let pr_step : P.t =
            match step with
            | SP.Hypothesis pr -> pr (* FIXME: should this have a special rule? *)

            | SP.Assumption ->
              (* push into assumptions and introduce a name for it *)
              let name = Printf.sprintf "a%d" !n_step in
              let lit = match concl with
                | [l] -> l
                | _ -> Error.errorf "assumption with non-unit clause %a" (SC.pp store) c
              in
              incr n_step;
              assms := (name, lit) :: !assms;
              P.ref_by_name name

            | Lemma pr -> pr

            | Duplicate (c, _) ->
              let n = find_proof_name c in
              let p = P.ref_by_name n in
              (* NOTE: we do not represent this form of transformation for now.
                 Quip should be able to process clauses as sets. *)
              p

            | Hyper_res { hr_init=init; hr_steps=steps } ->
              let proof_init = P.ref_by_name @@ find_proof_name init in
              let tr_step (pivot,p') : P.hres_step =
                (* unit resolution? *)
                let is_r1_step = SC.n_atoms store (SP.conclusion p') = 1 in
                let proof_p' = P.ref_by_name @@ find_proof_name p' in
                if is_r1_step then (
                  P.r1 proof_p'
                ) else (
                  let pivot = Lit.term (Sat_solver.Atom.formula store pivot) in
                  P.r proof_p' ~pivot
                )
              in
              P.hres_iter proof_init
                (Iter.of_list steps |> Iter.map tr_step)
          in

          let step = P.stepc ~name concl pr_step in
          add_step step;
        )
      in

      (* this should traverse from the leaves, so that order of [steps] is correct *)
      Sat_solver.Proof.fold store tr_node_to_step () msat;
      let assms = !assms in

      (* gather all term definitions *)
      let t_defs = CCList.map (fun (c,rhs) -> P.deft c rhs) t_defs in
      P.composite_l ~assms (CCList.append t_defs (List.rev !steps))

    let make solver (msat: Sat_solver.Proof.t) (tdefs: _ list) : t =
      { solver; msat; tdefs; p=lazy (conv_proof (Sat_solver.store solver) msat tdefs) }

    let check self = SP.check (Sat_solver.store self.solver) self.msat
    let pp_debug out self = P.pp_debug ~sharing:false out (to_proof self)
    let output oc (self:t) = P.Quip.output oc (to_proof self)
  end
     *)

  (* main solver state *)
  type t = {
    si: Solver_internal.t;
    solver: Sat_solver.t;
    stat: Stat.t;
    count_clause: int Stat.counter;
    count_solve: int Stat.counter;
    (* config: Config.t *)
  }
  type solver = t

  module Atom = struct
    include Sat_solver.Atom
    let pp self out a = pp (Sat_solver.store self.solver) out a
    let formula self a = formula (Sat_solver.store self.solver) a
  end

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
      si;
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
      Sat_solver.assume self.solver [
        [Lit.atom tst t_true];
      ] (fun p -> P.lemma_true p t_true)
    end;
    self

  let[@inline] solver self = self.solver
  let[@inline] cc self = Solver_internal.cc self.si
  let[@inline] stats self = self.stat
  let[@inline] tst self = Solver_internal.tst self.si
  let[@inline] ty_st self = Solver_internal.ty_st self.si

  let[@inline] mk_atom_lit_ self lit : Atom.t = Sat_solver.make_atom self.solver lit

  let mk_atom_t_ self t : Atom.t =
    let lit = Lit.atom (tst self) t in
    mk_atom_lit_ self lit

  (* map boolean subterms to literals *)
  let add_bool_subterms_ (self:t) (t:Term.t) : unit =
    Term.iter_dag t
    |> Iter.filter (fun t -> Ty.is_bool @@ Term.ty t)
    |> Iter.filter
      (fun t -> match A.cc_view t with
         | Sidekick_core.CC_view.Not _ -> false (* will process the subterm just later *)
         | _ -> true)
    |> Iter.filter (fun t -> A.is_valid_literal t)
    |> Iter.iter
      (fun sub ->
         Log.debugf 5 (fun k->k "(@[solver.map-bool-subterm-to-lit@ :subterm %a@])" Term.pp sub);
         (* ensure that SAT solver has a boolean atom for [sub] *)
         let atom = mk_atom_t_ self sub in
         (* also map [sub] to this atom in the congruence closure, for propagation *)
         let cc = cc self in
         let store = Sat_solver.store self.solver in
         CC.set_as_lit cc (CC.add_term cc sub ) (Sat_solver.Atom.formula store atom);
         ())

  let rec mk_atom_lit self lit : Atom.t * dproof =
    let lit, proof = preprocess_lit_ self lit in
    add_bool_subterms_ self (Lit.term lit);
    Sat_solver.make_atom self.solver lit, proof

  and preprocess_lit_ self lit : Lit.t * dproof =
    Solver_internal.preprocess_lit_
      ~add_clause:(fun lits proof ->
          (* recursively add these sub-literals, so they're also properly processed *)
          Stat.incr self.si.count_preprocess_clause;
          let pr_l = ref [] in
          let atoms =
            List.map
              (fun lit ->
                 let a, pr = mk_atom_lit self lit in
                 (* FIXME                 if not (P.is_trivial_refl pr) then ( *)
                   pr_l := pr :: !pr_l;
                   (*                  ); *)
                 a)
              lits
          in
          let emit_proof p = List.iter (fun dp -> dp p) !pr_l; in
          Sat_solver.add_clause self.solver atoms emit_proof)
      self.si lit

  let[@inline] mk_atom_t self ?sign t : Atom.t * dproof =
    let lit = Lit.atom (tst self) ?sign t in
    mk_atom_lit self lit

  let mk_atom_t' self ?sign t = mk_atom_t self ?sign t |> fst
  let mk_atom_lit' self lit = mk_atom_lit self lit |> fst

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
        unsat_core: Atom.t list lazy_t;
      }
    | Unknown of Unknown.t
    (** Result of solving for the current set of clauses *)

  (** {2 Main} *)

  let pp_stats out (self:t) : unit =
    Stat.pp_all out (Stat.all @@ stats self)

  let add_clause (self:t) (c:Atom.t IArray.t) (proof:dproof) : unit =
    Stat.incr self.count_clause;
    Log.debugf 50 (fun k->
        let store = Sat_solver.store self.solver in
        k "(@[solver.add-clause@ %a@])"
          (Util.pp_iarray (Sat_solver.Atom.pp store)) c);
    let pb = Profile.begin_ "add-clause" in
    Sat_solver.add_clause_a self.solver (c:> Atom.t array) proof;
    Profile.exit pb

  let add_clause_l self c p = add_clause self (IArray.of_list c) p

  let assert_terms self c =
    let c = CCList.map (fun t -> Lit.atom (tst self) t) c in
    let emit_proof p =
      P.emit_input_clause p (Iter.of_list c)
    in
    (* FIXME: just emit proofs on the fly? *)
    let c = CCList.map (mk_atom_lit' self) c in
    add_clause_l self c emit_proof

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
      let unsat_core = lazy (UNSAT.unsat_assumptions ()) in
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
