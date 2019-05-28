

(** {1 Implementation of a Solver using Msat} *)

module Vec = Msat.Vec
module Log = Msat.Log
module IM = Util.Int_map

module type ARG = sig
  include Sidekick_core.TERM_LIT_PROOF
  val cc_view : Term.t -> (Fun.t, Term.t, Term.t Iter.t) Sidekick_core.CC_view.t
end

module type S = Sidekick_core.SOLVER

module Make(A : ARG)
(*   : S with type A.Term.t = A.Term.t *)
= struct
  module T = A.Term
  module Lit = A.Lit
  type lit = Lit.t

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
    type k1 =
      | K1 : {
          k: 'a key;
          e: exn;
        } -> k1

    type t = k1 IM.t

    let empty = IM.empty

    let[@inline] mem k t = IM.mem (CC_key.id k) t

    let find (type a) (k : a key) (self:t) : a option =
      let (module K) = k in
      match IM.find K.id self with
      | K1 {e=K.Store v;_} -> Some v
      | _ -> None
      | exception Not_found -> None

    let add (type a) (k : a key) (v:a) (self:t) : t =
      let (module K) = k in
      IM.add K.id (K1 {k; e=K.Store v}) self
      
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
           | Some (K1 {k=(module K1) as key1; e=pair1; }), Some (K1{e=pair2;_}) ->
             match pair1, pair2 with
             | K1.Store v1, K1.Store v2 ->
               let v12 = K1.merge v1 v2 in (* merge content *)
               Some (K1 {k=key1; e=K1.Store v12; })
             | _ -> assert false)
        m1 m2

    let pp_pair out (K1 {k=(module K);e=x; _}) =
      match x with
      | K.Store x -> K.pp out x
      | _ -> assert false

    let pp out (self:t) =
      if IM.is_empty self then Fmt.string out "{}"
      else Fmt.fprintf out "{@[%a@]}" (Util.pp_seq pp_pair) (IM.values self)
  end

  (* the full argument to the congruence closure *)
  module A = struct
    include A

    module Data = Key_set
    module Actions = struct
      type t = {
        raise_conflict : 'a. Lit.t list -> Proof.t -> 'a;
        propagate : Lit.t -> reason:Lit.t Iter.t -> Proof.t -> unit;
      }
      let[@inline] raise_conflict a lits p = a.raise_conflict lits p
      let[@inline] propagate a lit ~reason p = a.propagate lit ~reason p
    end
  end

  module CC = Sidekick_cc.Make(A)
  module Expl = CC.Expl
  module N = CC.N

  (** Internal solver, given to theories and to Msat *)
  module Solver_internal = struct
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
      mutable on_cc_merge: on_cc_merge list IM.t;
      mutable on_cc_new_term : on_cc_new_term IM.t;
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
        on_cc_new_term=IM.empty;
      } in
      ignore (Lazy.force @@ self.cc : CC.t);
      self

  end

  type conflict = lit list

  (** the Main Solver *)
  module Sat_solver = Msat.Make_cdcl_t(Solver_internal)

  let[@inline] clause_of_mclause (c:Sat_solver.clause): Lit.t IArray.t =
    Sat_solver.Clause.atoms c |> Array.map Sat_solver.Atom.formula |> IArray.of_array_unsafe

  module Atom = Sat_solver.Atom
  module Proof = Sat_solver.Proof

  (* main solver state *)
  type t = {
    si: Solver_internal.t;
    solver: Sat_solver.t;
    stat: Stat.t;
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

  type res = (Model.t, Proof.t, lit IArray.t, Unknown.t) Sidekick_core.solver_res

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
    Term.iter_dag t
    |> Iter.filter (fun t -> Ty.is_prop @@ Term.ty t)
    |> Iter.filter
      (fun t -> match Term.view t with
         | Term.Not _ -> false (* will process the subterm just later *)
         | _ -> true)
    |> Iter.iter
      (fun sub ->
         Log.debugf 5 (fun k->k  "(@[solver.map-to-lit@ :subterm %a@])" Term.pp sub);
         ignore (mk_atom_t self sub : Sat_solver.atom))

  let assume (self:t) (c:Lit.t IArray.t) : unit =
    let sat = solver self in
    IArray.iter (fun lit -> add_bool_subterms_ self @@ Lit.term lit) c;
    let c = IArray.to_array_map (Sat_solver.make_atom sat) c in
    Stat.incr self.count_clause;
    Sat_solver.add_clause_a sat c Proof_default

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

  (* TODO: main loop with iterative deepening of the unrolling  limit
     (not the value depth limit) *)
  let solve ?(on_exit=[]) ?(check=true) ~assumptions (self:t) : res =
    let do_on_exit () =
      List.iter (fun f->f()) on_exit;
    in
    let r = Sat_solver.solve ~assumptions (solver self) in
    Stat.incr self.count_solve;
    match r with
    | Sat_solver.Sat st ->
      Log.debugf 1 (fun k->k "SAT");
      let lits f = st.iter_trail f (fun _ -> ()) in
      let m = Theory_combine.mk_model (th_combine self) lits in
      do_on_exit ();
      Sat m
      (*
      let env = Ast.env_empty in
      let m = Model.make ~env in
         …
      Unknown U_incomplete (* TODO *)
      *)
    | Sat_solver.Unsat us ->
      let pr =
        try
          let pr = us.get_proof () in
          if check then Sat_solver.Proof.check pr;
          Some pr
        with Msat.Solver_intf.No_proof -> None
      in
      do_on_exit ();
      Unsat pr

end
