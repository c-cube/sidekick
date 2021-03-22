(** {1 Implementation of a Solver using Msat} *)

module Log = Msat.Log

module type ARG = sig
  open Sidekick_core
  module T : TERM
  module P : PROOF

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t

  val is_valid_literal : T.Term.t -> bool
  (** Is this a valid boolean literal? (e.g. is it a closed term, not inside
      a quantifier) *)
end

module type S = Sidekick_core.SOLVER

module Make(A : ARG)
  : S
    with module T = A.T
     and module P = A.P
= struct
  module T = A.T
  module P = A.P
  module Ty = T.Ty
  module Term = T.Term
  type term = Term.t
  type ty = Ty.t
  type lemma = P.t

  module Lit_ = struct
    module T = T
    type t = {
      lit_term: term;
      lit_sign : bool
    }

    let[@inline] neg l = {l with lit_sign=not l.lit_sign}
    let[@inline] sign t = t.lit_sign
    let[@inline] abs t = {t with lit_sign=true}
    let[@inline] term (t:t): term = t.lit_term

    let make ~sign t = {lit_sign=sign; lit_term=t}

    let atom tst ?(sign=true) (t:term) : t =
      let t, sign' = Term.abs tst t in
      let sign = if not sign' then not sign else sign in
      make ~sign t

    let equal a b =
      a.lit_sign = b.lit_sign &&
      Term.equal a.lit_term b.lit_term

    let hash a =
      let sign = a.lit_sign in
      CCHash.combine3 2 (CCHash.bool sign) (Term.hash a.lit_term)

    let pp out l =
      if l.lit_sign then Term.pp out l.lit_term
      else Format.fprintf out "(@[@<1>¬@ %a@])" Term.pp l.lit_term

    let apply_sign t s = if s then t else neg t
    let norm_sign l = if l.lit_sign then l, true else neg l, false
    let norm l = let l, sign = norm_sign l in l, if sign then Msat.Same_sign else Msat.Negated
  end

  type lit = Lit_.t

  (* actions from msat *)
  type msat_acts = (Msat.void, lit, Msat.void, P.t) Msat.acts

  (* the full argument to the congruence closure *)
  module CC_actions = struct
    module T = T
    module P = P
    module Lit = Lit_
    let cc_view = A.cc_view

    module Actions = struct
      module T = T
      module P = P
      module Lit = Lit
      type t = msat_acts
      let[@inline] raise_conflict a lits pr =
        a.Msat.acts_raise_conflict lits pr
      let[@inline] propagate a lit ~reason pr =
        let reason = Msat.Consequence (fun () -> reason(), pr) in
        a.Msat.acts_propagate lit reason
    end
  end

  module CC = Sidekick_cc.Make(CC_actions)
  module Expl = CC.Expl
  module N = CC.N

  (** Internal solver, given to theories and to Msat *)
  module Solver_internal = struct
    module T = T
    module P = P
    module Lit = Lit_
    module CC = CC
    module N = CC.N
    type term = Term.t
    type ty = Ty.t
    type lit = Lit.t
    type term_state = Term.state
    type ty_state = Ty.state

    type th_states =
      | Ths_nil
      | Ths_cons : {
          st: 'a;
          push_level: 'a -> unit;
          pop_levels: 'a -> int -> unit;
          next: th_states;
        } -> th_states

    type actions = msat_acts

    module Simplify = struct
      type t = {
        tst: term_state;
        ty_st: ty_state;
        mutable hooks: hook list;
        cache: Term.t Term.Tbl.t;
      }
      and hook = t -> term -> term option

      let create tst ty_st : t =
        {tst; ty_st; hooks=[]; cache=Term.Tbl.create 32;}
      let[@inline] tst self = self.tst
      let[@inline] ty_st self = self.ty_st
      let add_hook self f = self.hooks <- f :: self.hooks
      let clear self = Term.Tbl.clear self.cache

      let normalize (self:t) (t:Term.t) : Term.t =
        (* compute and cache normal form of [t] *)
        let rec aux t =
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
            | Some u -> aux u
        in
        aux t
    end
    type simplify_hook = Simplify.hook

    type t = {
      tst: Term.state; (** state for managing terms *)
      ty_st: Ty.state;
      cc: CC.t lazy_t; (** congruence closure *)
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
      mutable th_states : th_states; (** Set of theories *)
      mutable on_partial_check: (t -> actions -> lit Iter.t -> unit) list;
      mutable on_final_check: (t -> actions -> lit Iter.t -> unit) list;
      mutable level: int;
    }

    and preprocess_hook =
      t ->
      mk_lit:(term -> lit) ->
      add_clause:(lit list -> unit) ->
      term -> term option

    and model_hook =
      recurse:(t -> CC.N.t -> term) ->
      t -> CC.N.t -> term option

    type solver = t

    module Formula = struct
      include Lit
      let norm lit =
        let lit', sign = norm_sign lit in
        lit', if sign then Msat.Same_sign else Msat.Negated
    end
    module Eq_class = CC.N
    module Expl = CC.Expl

    type proof = P.t

    let[@inline] cc (t:t) = Lazy.force t.cc
    let[@inline] tst t = t.tst
    let[@inline] ty_st t = t.ty_st
    let stats t = t.stat

    let simplifier self = self.simp
    let simp_t self (t:Term.t) : Term.t = Simplify.normalize self.simp t
    let add_simplifier (self:t) f : unit = Simplify.add_hook self.simp f

    let on_preprocess self f = self.preprocess <- f :: self.preprocess
    let on_model_gen self f = self.mk_model <- f :: self.mk_model

    let push_decision (_self:t) (acts:actions) (lit:lit) : unit =
      let sign = Lit.sign lit in
      acts.Msat.acts_add_decision_lit (Lit.abs lit) sign

    let[@inline] raise_conflict self acts c : 'a =
      Stat.incr self.count_conflict;
      acts.Msat.acts_raise_conflict c P.default

    let[@inline] propagate self acts p cs : unit =
      Stat.incr self.count_propagate;
      acts.Msat.acts_propagate p (Msat.Consequence (fun () -> cs(), P.default))

    let[@inline] propagate_l self acts p cs : unit =
      propagate self acts p (fun()->cs)

    let add_sat_clause_ self acts ~keep lits : unit =
      Stat.incr self.count_axiom;
      acts.Msat.acts_add_clause ~keep lits P.default

    let preprocess_term_ (self:t) ~add_clause (t:term) : term =
      let mk_lit t = Lit.atom self.tst t in (* no further simplification *)

      (* compute and cache normal form of [t] *)
      let rec aux t =
        match Term.Tbl.find self.preprocess_cache t with
        | u -> u
        | exception Not_found ->
          (* try rewrite at root *)
          let t1 = aux_rec t self.preprocess in
          (* then map subterms *)
          let t2 = Term.map_shallow self.tst aux t1 in (* map subterms *)
          let u = if t != t2 then aux t2 (* fixpoint *) else t2 in

          if t != u then (
            Log.debugf 5
              (fun k->k "(@[msat-solver.preprocess.term@ \
                         :from %a@ :to %a@])" Term.pp t Term.pp u);
          );

          Term.Tbl.add self.preprocess_cache t u;
          u
      (* try each function in [hooks] successively *)
      and aux_rec t hooks = match hooks with
        | [] -> t
        | h :: hooks_tl ->
          match h self ~mk_lit ~add_clause t with
          | None -> aux_rec t hooks_tl
          | Some u -> aux u
      in
      t |> simp_t self |> aux

    let preprocess_lit_ (self:t) ~add_clause (lit:lit) : lit =
      let t = Lit.term lit |> preprocess_term_ self ~add_clause in
      let lit' = Lit.atom self.tst ~sign:(Lit.sign lit) t in
      Log.debugf 10
        (fun k->k "(@[msat-solver.preprocess.lit@ :lit %a@ :into %a@])" Lit.pp lit Lit.pp lit');
      lit'

    (* add a clause using [acts] *)
    let add_clause_ self acts lits : unit =
      Stat.incr self.count_preprocess_clause;
      add_sat_clause_ self acts ~keep:true lits

    let mk_lit self acts ?sign t =
      let add_clause = add_clause_ self acts in
      preprocess_lit_ self ~add_clause @@ Lit.atom self.tst ?sign t

    let[@inline] preprocess_term self ~add_clause (t:term) : term =
      preprocess_term_ self ~add_clause t

    let[@inline] add_clause_temp self acts lits : unit =
      add_sat_clause_ self acts ~keep:false lits

    let[@inline] add_clause_permanent self acts lits : unit =
      add_sat_clause_ self acts ~keep:true lits

    let add_lit _self acts lit : unit = acts.Msat.acts_mk_lit lit

    let add_lit_t self acts ?sign t = add_lit self acts (mk_lit self acts ?sign t)

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
      Msat.Log.debugf 2
        (fun k->k "(@[<hv1>@{<green>msat-solver.assume_lits@}%s[lvl=%d]@ %a@])"
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

    let[@inline] iter_atoms_ acts : _ Iter.t =
      fun f ->
      acts.Msat.acts_iter_assumptions
        (function
          | Msat.Lit a -> f a
          | Msat.Assign _ -> assert false)

    (* propagation from the bool solver *)
    let check_ ~final (self:t) (acts: msat_acts) =
      let pb = if final then Profile.begin_ "solver.final-check" else Profile.null_probe in
      let iter = iter_atoms_ acts in
      Msat.Log.debugf 5 (fun k->k "(msat-solver.assume :len %d)" (Iter.length iter));
      self.on_progress();
      assert_lits_ ~final self acts iter;
      Profile.exit pb

    (* propagation from the bool solver *)
    let[@inline] partial_check (self:t) (acts:_ Msat.acts) : unit =
      check_ ~final:false self acts

    (* perform final check of the model *)
    let[@inline] final_check (self:t) (acts:_ Msat.acts) : unit =
      check_ ~final:true self acts

    let create ~stat (tst:Term.state) (ty_st:Ty.state) () : t =
      let rec self = {
        tst;
        ty_st;
        cc = lazy (
          (* lazily tie the knot *)
          CC.create ~size:`Big self.tst;
        );
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
        on_partial_check=[];
        on_final_check=[];
        level=0;
      } in
      ignore (Lazy.force @@ self.cc : CC.t);
      self
  end
  module Lit = Solver_internal.Lit

  (** the parametrized SAT Solver *)
  module Sat_solver = Msat.Make_cdcl_t(Solver_internal)

  module Atom = Sat_solver.Atom
  module Proof = struct
    include Sat_solver.Proof
    module Dot = Msat_backend.Dot.Make(Sat_solver)(Msat_backend.Dot.Default(Sat_solver))
    let pp_dot = Dot.pp
  end

  type proof = Proof.t

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
      (fun k-> k "(@[msat-solver.add-theory@ :name %S@])" Th.name);
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
  let create ?(stat=Stat.global) ?size ?store_proof ~theories tst ty_st () : t =
    Log.debug 5 "msat-solver.create";
    let si = Solver_internal.create ~stat tst ty_st () in
    let self = {
      si;
      solver=Sat_solver.create ?store_proof ?size si;
      stat;
      count_clause=Stat.mk_int stat "solver.add-clause";
      count_solve=Stat.mk_int stat "solver.solve";
    } in
    add_theory_l self theories;
    (* assert [true] and [not false] *)
    begin
      let tst = Solver_internal.tst self.si in
      Sat_solver.assume self.solver [
        [Lit.atom tst @@ Term.bool tst true];
      ] P.default;
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
         (* ensure that msat has a boolean atom for [sub] *)
         let atom = mk_atom_t_ self sub in
         (* also map [sub] to this atom in the congruence closure, for propagation *)
         let cc = cc self in
         CC.set_as_lit cc (CC.add_term cc sub ) (Sat_solver.Atom.formula atom);
         ())

  let rec mk_atom_lit self lit : Atom.t =
    let lit = preprocess_lit_ self lit in
    add_bool_subterms_ self (Lit.term lit);
    Sat_solver.make_atom self.solver lit

  and preprocess_lit_ self lit : Lit.t =
      Solver_internal.preprocess_lit_
        ~add_clause:(fun lits ->
            (* recursively add these sub-literals, so they're also properly processed *)
            Stat.incr self.si.count_preprocess_clause;
            let atoms = List.map (mk_atom_lit self) lits in
            Sat_solver.add_clause self.solver atoms P.default)
        self.si lit

  let[@inline] mk_atom_t self ?sign t : Atom.t =
    let lit = Lit.atom (tst self) ?sign t in
    mk_atom_lit self lit

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
        proof: proof option lazy_t;
        unsat_core: Atom.t list lazy_t;
      }
    | Unknown of Unknown.t
    (** Result of solving for the current set of clauses *)

  (** {2 Main} *)

  let pp_stats out (self:t) : unit =
    Stat.pp_all out (Stat.all @@ stats self)

  let add_clause (self:t) (c:Atom.t IArray.t) : unit =
    Stat.incr self.count_clause;
    Log.debugf 50 (fun k->k "(@[solver.add-clause@ %a@])" (Util.pp_iarray Atom.pp) c);
    let pb = Profile.begin_ "add-clause" in
    Sat_solver.add_clause_a self.solver (c:> Atom.t array) P.default;
    Profile.exit pb

  let add_clause_l self c = add_clause self (IArray.of_list c)


    (* TODO
    let mk_model (self:t) lits : Model.t =
      let m =
        Iter.fold
          (fun m (Th_state ((module Th),st)) -> Th.mk_model st lits m)
          Model.empty (theories self)
      in
      (* now complete model using CC *)
      CC.mk_model (cc self) m
       *)

  let mk_model (self:t) (lits:lit Iter.t) : Model.t =
    Log.debug 1 "(smt.solver.mk-model)";
    Profile.with_ "msat-solver.mk-model" @@ fun () ->
    let module M = Term.Tbl in
    let model = M.create 128 in
    let {Solver_internal.tst; cc=lazy cc; mk_model=model_hooks; _} = self.si in

    (* first, add all literals to the model using the given propositional model
       [lits]. *)
    lits
      (fun {Lit.lit_term=t;lit_sign=sign} ->
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
    Profile.with_ "msat-solver.solve" @@ fun () ->
    let do_on_exit () =
      List.iter (fun f->f()) on_exit;
    in
    self.si.on_progress <- (fun () -> on_progress self);
    let r = Sat_solver.solve ~assumptions (solver self) in
    Stat.incr self.count_solve;
    match r with
    | Sat_solver.Sat st ->
      Log.debug 1 "sidekick.msat-solver: SAT";
      let _lits f = st.iter_trail f (fun _ -> ()) in
      (* TODO: theory combination *)
      let m = mk_model self _lits in
      do_on_exit ();
      Sat m
    | Sat_solver.Unsat us ->
      let proof = lazy (
        try
          let pr = us.get_proof () in
          if check then Sat_solver.Proof.check pr;
          Some pr
        with Msat.Solver_intf.No_proof -> None
      ) in
      let unsat_core = lazy (us.Msat.unsat_assumptions ()) in
      do_on_exit ();
      Unsat {proof; unsat_core}

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
