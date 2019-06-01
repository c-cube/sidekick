

(** {1 Implementation of a Solver using Msat} *)

module Vec = Msat.Vec
module Log = Msat.Log
module IM = Util.Int_map
module CC_view = Sidekick_core.CC_view

module type ARG = sig
  module A : Sidekick_core.CORE_TYPES
  open A
  val cc_view : Term.t -> (Fun.t, Term.t, Term.t Iter.t) CC_view.t
end

module type S = Sidekick_core.SOLVER

module Make(Solver_arg : ARG)
(*   : S with module A = Solver_arg.A *)
= struct
  module A = Solver_arg.A
  module T = A.Term
  module Ty = A.Ty
  module Lit = A.Lit
  type term = T.t
  type ty = Ty.t
  type lit = Lit.t
  type value = A.Value.t

  (** Custom keys for theory data.
      This imitates the classic tricks for heterogeneous maps
      https://blog.janestreet.com/a-universal-type/

      It needs to form a commutative monoid where values are persistent so
      they can be restored during backtracking.
  *)
  module CC_key = struct
    type 'a data = (module Sidekick_core.MERGE_PP with type t = 'a)
    module type KEY_IMPL = sig
      include Sidekick_core.MERGE_PP
      val id : int
      exception Store of t
    end

    type 'a t = (module KEY_IMPL with type t = 'a)

    let n_ = ref 0

    let create (type d) (x:d data) : d t =
      let (module D) = x in
      let module K = struct
        include D
        let id = !n_
        exception Store of t
      end in
      incr n_;
      (module K)

    let[@inline] id : type a. a t -> int = fun (module K) -> K.id

    let[@inline] equal
      : type a b. a t -> b t -> bool
      = fun (module K1) (module K2) -> K1.id = K2.id

    let pp
      : type a. a t -> a Fmt.printer
      = fun (module K) out x -> K.pp out x
  end

  (** Map for theory data associated with representatives, given
      to the congruence closure. *)
  module Key_set = struct
    type 'a key = 'a CC_key.t

    type ke =
      | KE : {
          k: 'a key;
          e: exn;
        } -> ke

    type t = ke IM.t

    let empty = IM.empty
    let is_empty = IM.is_empty

    let[@inline] mem k t = IM.mem (CC_key.id k) t

    (** Find the content for this key.
        @raise Not_found if not present *)
    let find (type a) (k : a key) (self:t) : a =
      let (module K) = k in
      match IM.find K.id self with
      | KE {e=K.Store v;_} -> v
      | _ -> raise_notrace Not_found

    let[@inline] find_opt k self = try Some (find k self) with Not_found -> None

    let add (type a) (k : a key) (v:a) (self:t) : t =
      let (module K) = k in
      IM.add K.id (KE {k; e=K.Store v}) self
      
    let remove (type a) (k: a key) self : t =
      let (module K) = k in
      IM.remove K.id self

    let merge (m1:t) (m2:t) : t =
      IM.merge
        (fun _ p1 p2 ->
           match p1, p2 with
           | None, None -> None
           | Some v, None
           | None, Some v -> Some v
           | Some (KE {k=(module KE) as key1; e=pair1; }), Some (KE{e=pair2;_}) ->
             match pair1, pair2 with
             | KE.Store v1, KE.Store v2 ->
               let v12 = KE.merge v1 v2 in (* merge content *)
               Some (KE {k=key1; e=KE.Store v12; })
             | _ -> assert false)
        m1 m2

    type iter_fun = {
      iter_fun: 'a. 'a key -> 'a -> 'a -> unit;
    } [@@unboxed]

    let iter_inter (f: iter_fun) (m1:t) (m2:t) : unit =
      if is_empty m1 || is_empty m2 then ()
      else (
        IM.iter
          (fun i (KE {k=(module Key) as key;e=e1}) ->
             match IM.find i m2 with
             | KE {e=e2;_} ->
               begin match e1, e2 with
                 | Key.Store x, Key.Store y -> f.iter_fun key x y
                 | _ -> assert false
               end
             | exception Not_found -> ())
          m1
      )

    let pp_pair out (KE {k=(module K);e=x; _}) =
      match x with
      | K.Store x -> K.pp out x
      | _ -> assert false

    let pp out (self:t) =
      if IM.is_empty self then Fmt.string out "{}"
      else Fmt.fprintf out "{@[%a@]}" (Util.pp_seq pp_pair) (IM.values self)
  end

  (* the full argument to the congruence closure *)
  module CC_A = struct
    include Solver_arg

    module Data = Key_set
    module Actions = struct
      type t = {
        raise_conflict : 'a. Lit.t list -> A.Proof.t -> 'a;
        propagate : Lit.t -> reason:Lit.t Iter.t -> A.Proof.t -> unit;
      }
      let[@inline] raise_conflict a lits p = a.raise_conflict lits p
      let[@inline] propagate a lit ~reason p = a.propagate lit ~reason p
    end
  end

  module CC = Sidekick_cc.Make(CC_A)
  module Expl = CC.Expl
  module N = CC.N

  (** Internal solver, given to theories and to Msat *)
  module Solver_internal
      : Sidekick_core.SOLVER_INTERNAL with module A = A
  = struct
    module A = A

    type th_states = 
      | Ths_nil
      | Ths_cons : {
          st: 'a;
          push_level: 'a -> unit;
          pop_levels: 'a -> int -> unit;
          next: th_states;
        } -> th_states

    (* actions from msat *)
    type msat_acts = (Msat.void, Lit.t, Msat.void, A.Proof.t) Msat.acts

    type t = {
      tst: T.state; (** state for managing terms *)
      cc: CC.t lazy_t; (** congruence closure *)
      stat: Stat.t;
      count_axiom: int Stat.counter;
      count_conflict: int Stat.counter;
      count_propagate: int Stat.counter;
      cc_acts: CC.actions lazy_t;
      mutable th_states : th_states; (** Set of theories *)
      mutable msat_acts: msat_acts option;
      mutable on_partial_check: (t -> lit Iter.t -> unit) list;
      mutable on_final_check: (t -> lit Iter.t -> unit) list;
      mutable on_cc_merge: on_cc_merge IM.t;
      mutable on_cc_new_term : on_cc_new_term list;
    }

    and on_cc_merge = On_cc_merge : {
        k: 'a CC_key.t;
        f: t -> CC.N.t -> 'a -> CC.N.t -> 'a -> CC.Expl.t -> unit;
      } -> on_cc_merge

    and on_cc_new_term = On_cc_new_term : {
        k: 'a CC_key.t;
        f: t -> N.t -> T.t -> 'a option;
      } -> on_cc_new_term

    module Formula = struct
      include Lit
      let norm lit =
        let lit', sign = norm_sign lit in
        lit', if sign then Msat.Same_sign else Msat.Negated
    end
    module Eq_class = CC.N
    module Expl = CC.Expl

    type formula = Lit.t
    type proof = A.Proof.t
    type conflict = lit list

    let[@inline] cc (t:t) = Lazy.force t.cc
    let[@inline] tst t = t.tst

    let on_cc_merge self ~k f =
      self.on_cc_merge <- IM.add (CC_key.id k) (On_cc_merge{k;f}) self.on_cc_merge

    let on_cc_new_term self ~k f =
      self.on_cc_new_term <- On_cc_new_term {k;f} :: self.on_cc_new_term

    let on_cc_merge_all self f =
      (* just delegate this to the CC *)
      CC.on_merge (cc self) (fun _cc n1 _th1 n2 _th2 expl -> f self n1 n2 expl)

    let handle_on_cc_merge (self:t) _cc n1 th1 n2 th2 expl : unit =
      if Key_set.is_empty th1 || Key_set.is_empty th2 then ()
      else (
        (* iterate over the intersection of [th1] and [th2] *)
        IM.iter
          (fun _ (On_cc_merge {f;k}) ->
             match Key_set.find k th1, Key_set.find k th2 with
             | x1, x2 -> f self n1 x1 n2 x2 expl
             | exception Not_found -> ())
          self.on_cc_merge
      )

    (* called by the CC when a term is added *)
    let handle_on_cc_new_term (self:t) _cc n1 t1 : _ option =
      match self.on_cc_new_term with
      | [] -> None
      | l ->
        let map =
          List.fold_left
            (fun map (On_cc_new_term{k;f}) ->
               match f self n1 t1 with
               | None -> map
               | Some u -> Key_set.add k u map)
            Key_set.empty l
        in
        if Key_set.is_empty map then None else Some map

    let[@inline] raise_conflict self c : 'a =
      Stat.incr self.count_conflict;
      match self.msat_acts with
      | None -> assert false
      | Some acts ->
        acts.Msat.acts_raise_conflict c A.Proof.default

    let[@inline] propagate self p cs : unit =
      Stat.incr self.count_propagate;
      match self.msat_acts with
      | None -> assert false
      | Some acts ->
        acts.Msat.acts_propagate p (Msat.Consequence (fun () -> cs(), A.Proof.default))

    let[@inline] propagate_l self p cs : unit = propagate self p (fun()->cs)

    let[@inline] cc_add_term self t = CC.add_term (cc self) t
    let[@inline] cc_merge self n1 n2 e = CC.Theory.merge (cc self) n1 n2 e
    let cc_merge_t self t1 t2 e =
      let lazy cc = self.cc in
      CC.Theory.merge cc (CC.add_term cc t1) (CC.add_term cc t2) e

    let cc_data self ~k n =
      let data = N.th_data (CC.find (cc self) n) in
      Key_set.find_opt k data

    let add_axiom_ self ~keep lits : unit =
      Stat.incr self.count_axiom;
      match self.msat_acts with
      | None -> assert false
      | Some acts ->
        acts.Msat.acts_add_clause ~keep lits A.Proof.default

    let[@inline] mk_lit self ?sign t = Lit.atom self.tst ?sign t

    let[@inline] add_local_axiom self lits : unit =
      add_axiom_ self ~keep:false lits

    let[@inline] add_persistent_axiom self lits : unit =
      add_axiom_ self ~keep:true lits

    let[@inline] add_lit self lit : unit =
      match self.msat_acts with
      | None -> assert false
      | Some acts -> acts.Msat.acts_mk_lit lit

    let add_lit_t self ?sign t = add_lit self (mk_lit self ?sign t)

    (** {2 Interface with the SAT solver} *)

    let rec push_lvl_ = function
      | Ths_nil -> ()
      | Ths_cons r -> r.push_level r.st; push_lvl_ r.next

    let rec pop_lvls_ n = function
      | Ths_nil -> ()
      | Ths_cons r -> r.pop_levels r.st n; pop_lvls_ n r.next

    let push_level (self:t) : unit =
      CC.push_level (cc self);
      push_lvl_ self.th_states

    let pop_levels (self:t) n : unit =
      CC.pop_levels (cc self) n;
      pop_lvls_ n self.th_states

    (* handle a literal assumed by the SAT solver *)
    let assert_lits_ ~final (self:t) (lits:Lit.t Iter.t) : unit =
      Msat.Log.debugf 2
        (fun k->k "(@[<hv1>@{<green>th_combine.assume_lits@}%s@ %a@])"
            (if final then "[final]" else "") (Util.pp_seq ~sep:"; " Lit.pp) lits);
      (* transmit to CC *)
      let cc = cc self in
      if not final then (
        CC.assert_lits cc lits;
      );
      (* transmit to theories. *)
      CC.check cc (Lazy.force self.cc_acts);
      if final then (
        List.iter (fun f -> f self lits) self.on_final_check;
      ) else (
        List.iter (fun f -> f self lits) self.on_partial_check;
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
      let old_acts = self.msat_acts in
      self.msat_acts <- Some acts;
      try
        let iter = iter_atoms_ acts in
        (* TODO if Config.progress then print_progress(); *)
        Msat.Log.debugf 5 (fun k->k "(th_combine.assume :len %d)" (Iter.length iter));
        assert_lits_ ~final self iter;
        self.msat_acts <- old_acts;
        ()
      with e ->
        self.msat_acts <- old_acts;
        raise e

    let add_formula (self:t) (lit:Lit.t) =
      let t = Lit.term lit in
      let lazy cc = self.cc in
      let n = CC.add_term cc t in
      CC.set_as_lit cc n (Lit.abs lit);
      ()

    let on_final_check self f = self.on_final_check <- f :: self.on_final_check
    let on_partial_check self f = self.on_partial_check <- f :: self.on_partial_check

    (* propagation from the bool solver *)
    let[@inline] partial_check (self:t) (acts:_ Msat.acts) : unit =
      check_ ~final:false self acts

    (* perform final check of the model *)
    let[@inline] final_check (self:t) (acts:_ Msat.acts) : unit =
      check_ ~final:true self acts

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

    let cc_raise_conflict self lits _p =
      raise_conflict self lits

    let cc_propagate self p ~reason _p =
      let reason() = Iter.to_list reason in
      propagate self p reason

    let create ~stat (tst:A.Term.state) () : t =
      let rec self = {
        tst;
        cc = lazy (
          (* lazily tie the knot *)
          CC.create ~size:`Big self.tst;
        );
        cc_acts=lazy {
          raise_conflict=cc_raise_conflict self;
          propagate=cc_propagate self;
        };
        th_states=Ths_nil;
        stat;
        count_axiom = Stat.mk_int stat "th-axioms";
        count_propagate = Stat.mk_int stat "th-propagations";
        count_conflict = Stat.mk_int stat "th-conflicts";
        msat_acts=None;
        on_partial_check=[];
        on_final_check=[];
        on_cc_merge=IM.empty;
        on_cc_new_term=[];
      } in
      let lazy cc = self.cc in
      CC.on_merge cc (handle_on_cc_merge self);
      CC.on_new_term cc (handle_on_cc_new_term self);
      self
  end

  type conflict = lit list

  (** the Main Solver *)
  module Sat_solver = Msat.Make_cdcl_t(Solver_internal)

  let[@inline] clause_of_mclause (c:Sat_solver.clause): Lit.t IArray.t =
    Sat_solver.Clause.atoms c |> Array.map Sat_solver.Atom.formula |> IArray.of_array_unsafe

  module Atom = Sat_solver.Atom
  module Proof = Sat_solver.Proof
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

  let mk_theory (type st)
      ~name ~create_and_setup
      ?(push_level=fun _ -> ())
      ?(pop_levels=fun _ _ -> ())
      () : theory =
    let module Th = struct
      type t = st
      let name = name
      let create_and_setup = create_and_setup
      let push_level = push_level
      let pop_levels = pop_levels
     end in
    (module Th : THEORY)

  (** {2 Main} *)

  let add_theory (self:t) (th:theory) : unit =
    let (module Th) = th in
    Log.debugf 2
      (fun k-> k "(@[th_combine.add_th@ :name %S@])" Th.name);
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
    ()

  let add_theory_l self = List.iter (add_theory self)

  (* create a new solver *)
  let create ?(stat=Stat.global) ?size ?store_proof ~theories tst () : t =
    Log.debug 5 "th_combine.create";
    let si = Solver_internal.create ~stat tst () in
    let self = {
      si;
      solver=Sat_solver.create ?store_proof ?size si;
      stat;
      count_clause=Stat.mk_int stat "solver-clauses";
      count_solve=Stat.mk_int stat "solver-solve";
    } in
    add_theory_l self theories;
    (* assert [true] and [not false] *)
    begin
      let tst = Solver_internal.tst self.si in
      Sat_solver.assume self.solver [
        [Lit.atom tst @@ T.bool tst true];
      ] A.Proof.default;
    end;
    self

  let check_invariants (self:t) =
    if Util._CHECK_INVARIANTS then (
      CC.Debug_.check_invariants (Solver_internal.cc self.si);
    )

  let[@inline] solver self = self.solver
  let[@inline] cc self = Solver_internal.cc self.si
  let stats self = self.stat
  let[@inline] tst self = Solver_internal.tst self.si

  let[@inline] mk_atom_lit self lit : Atom.t = Sat_solver.make_atom self.solver lit
  let[@inline] mk_atom_t self ?sign t : Atom.t =
    let lit = Lit.atom (tst self) ?sign t in
    mk_atom_lit self lit

  let add_clause self c = Sat_solver.add_clause_a self.solver (c:_ IArray.t:>_ array) A.Proof.default 
  let add_clause_l self l = add_clause self (IArray.of_list l)

  let add_clause_lits self l =
    add_clause self @@ IArray.map (mk_atom_lit self) l

  let add_clause_lits_l self l =
    add_clause self @@ IArray.of_list_map (mk_atom_lit self) l

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
  end

  (* TODO *)
  module Model = struct
    type t = unit
    let empty = ()
    let mem _ _ = false
    let find _ _ = None
    let eval _ _ = None
    let pp out _ = Fmt.string out "<model>"
  end

  (* TODO
  type model = A.Model.t
  let pp_model = Model.pp
     *)

  type res = (Model.t, Proof.t, unit ->lit IArray.t, Unknown.t) Sidekick_core.solver_res

  (** {2 Main} *)

  (* convert unsat-core *)
  let clauses_of_unsat_core (core:Sat_solver.clause list): Lit.t IArray.t Iter.t =
    Iter.of_list core
    |> Iter.map clause_of_mclause

  (* print all terms reachable from watched literals *)
  let pp_term_graph _out (_:t) =
    ()

  let pp_stats out (self:t) : unit =
    Stat.pp_all out (Stat.all @@ stats self)

  (* map boolean subterms to literals *)
  let add_bool_subterms_ (self:t) (t:T.t) : unit =
    T.iter_dag t
    |> Iter.filter (fun t -> Ty.is_bool @@ T.ty t)
    |> Iter.filter
      (fun t -> match CC_A.cc_view t with
         | CC_view.Not _ -> false (* will process the subterm just later *)
         | _ -> true)
    |> Iter.iter
      (fun sub ->
         Log.debugf 5 (fun k->k  "(@[solver.map-to-lit@ :subterm %a@])" T.pp sub);
         ignore (mk_atom_t self sub : Sat_solver.atom))

  let assume (self:t) (c:Lit.t IArray.t) : unit =
    let sat = solver self in
    IArray.iter (fun lit -> add_bool_subterms_ self @@ Lit.term lit) c;
    let c = IArray.to_array_map (Sat_solver.make_atom sat) c in
    Stat.incr self.count_clause;
    Sat_solver.add_clause_a sat c A.Proof.default

  (* TODO: remove? use a special constant + micro theory instead?
  let[@inline] assume_distinct self l ~neq lit : unit =
    CC.assert_distinct (cc self) l lit ~neq
     *)

  let check_model (_s:t) : unit =
    Log.debug 1 "(smt.solver.check-model)";
    (* TODO
    Sat_solver.check_model s.solver
    *)
    ()

  let solve ?(on_exit=[]) ?(check=true) ~assumptions (self:t) : res =
    let do_on_exit () =
      List.iter (fun f->f()) on_exit;
    in
    let r = Sat_solver.solve ~assumptions (solver self) in
    Stat.incr self.count_solve;
    match r with
    | Sat_solver.Sat st ->
      Log.debugf 1 (fun k->k "SAT");
      let _lits f = st.iter_trail f (fun _ -> ()) in
      let m = Model.empty in
      (* TODO Theory_combine.mk_model (th_combine self) lits  *)
      do_on_exit ();
      Sat m
    | Sat_solver.Unsat us ->
      let uc () =
        clause_of_mclause @@ us.Msat.unsat_conflict ()
      in
      let pr =
        try
          let pr = us.get_proof () in
          if check then Sat_solver.Proof.check pr;
          Some pr
        with Msat.Solver_intf.No_proof -> None
      in
      do_on_exit ();
      Unsat {proof=pr; unsat_core=uc}

end
