
(** {1 Theory for datatypes} *)

(** {2 Views} *)

(** Datatype-oriented view of terms.
    ['c] is the representation of constructors
    ['t] is the representation of terms
*)
type ('c,'t) data_view =
  | T_cstor of 'c * 't IArray.t
  | T_select of 'c * int * 't
  | T_is_a of 'c * 't
  | T_other of 't

(** View of types in a way that is directly useful for the theory of datatypes *)
type ('c, 'ty) data_ty_view =
  | Ty_arrow of 'ty Iter.t * 'ty
  | Ty_app of {
      args: 'ty Iter.t;
    }
  | Ty_data of {
      cstors: 'c;
    }
  | Ty_other

let name = "th-data"

(** An abtract representation of a datatype *)
module type DATA_TY = sig
  type t
  type cstor

  val equal : t -> t -> bool

  val finite : t -> bool

  val set_finite : t -> bool -> unit

  val view : t -> (cstor, t) data_ty_view

  val cstor_args : cstor -> t Iter.t

  (** A table indexed by types. *)
  module Tbl : Hashtbl.S with type key = t
end

(** {2 Cardinality of types} *)

module C = struct
  type t =
    | Finite
    | Infinite

  let (+) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
  let ( * ) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
  let ( ^ ) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
  let sum = Iter.fold (+) Finite
  let product = Iter.fold ( * ) Finite
end

module type ARG = sig
  module S : Sidekick_core.SOLVER

  module Cstor : sig
    type t
    val ty_args : t -> S.T.Ty.t Iter.t
    val pp : t Fmt.printer
    val equal : t -> t -> bool
  end

  val as_datatype : S.T.Ty.t -> (Cstor.t Iter.t, S.T.Ty.t) data_ty_view
  val view_as_data : S.T.Term.t -> (Cstor.t, S.T.Term.t) data_view
  val mk_cstor : S.T.Term.state -> Cstor.t -> S.T.Term.t IArray.t -> S.T.Term.t
  val mk_is_a: S.T.Term.state -> Cstor.t -> S.T.Term.t -> S.T.Term.t
  val mk_sel : S.T.Term.state -> Cstor.t -> int -> S.T.Term.t -> S.T.Term.t
  val ty_is_finite : S.T.Ty.t -> bool
  val ty_set_is_finite : S.T.Ty.t -> bool -> unit
end

(** Helper to compute the cardinality of types *)
module Compute_card(A : ARG) : sig
  type t
  val create : unit -> t
  val is_finite : t -> A.S.T.Ty.t -> bool
end = struct
  module Ty = A.S.T.Ty
  module Ty_tbl = CCHashtbl.Make(Ty)
  type t = {
    cards: C.t Ty_tbl.t;
  }

  let create() : t = { cards=Ty_tbl.create 16}

  let card (self:t) (ty:Ty.t) : C.t =
    let rec aux (ty:Ty.t) : C.t =
      match Ty_tbl.find self.cards ty with
      | c -> c
      | exception Not_found ->
        Ty_tbl.add self.cards ty C.Infinite; (* temp value, for fixpoint computation *)
        let c = match A.as_datatype ty with
          | Ty_other -> if A.ty_is_finite ty then C.Finite else C.Infinite
          | Ty_app {args} -> Iter.map aux args |> C.product
          | Ty_arrow (args,ret) ->
            C.( (aux ret) ^ (C.product @@ Iter.map aux args))
          | Ty_data { cstors; } ->
            let c =
              cstors
              |> Iter.map (fun c -> C.product (Iter.map aux @@ A.Cstor.ty_args c))
              |> C.sum
            in
            A.ty_set_is_finite ty (c=Finite);
            c
        in
        Ty_tbl.replace self.cards ty c;
        c
    in
    aux ty

  let is_finite self ty : bool =
    match card self ty with
    | C.Finite -> true
    | C.Infinite -> false
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module SI = A.S.Solver_internal
  module T = A.S.T.Term
  module N = SI.CC.N
  module Ty = A.S.T.Ty
  module Fun = A.S.T.Fun
  module Expl = SI.CC.Expl

  module Card = Compute_card(A)

  (** Monoid mapping each class to the (unique) constructor it contains,
      if any *)
  module Monoid_cstor = struct
    module SI = SI
    let name = "th-data.cstor"

    (* associate to each class a unique constructor term in the class (if any) *)
    type t = {
      c_n: N.t;
      c_cstor: A.Cstor.t;
      c_args: T.t IArray.t;
    }

    let pp out (v:t) =
      Fmt.fprintf out "(@[%s@ :cstor %a@ :n %a@])" name A.Cstor.pp v.c_cstor N.pp v.c_n

    (* attach data to constructor terms *)
    let of_term n (t:T.t) : _ option * _ list =
      match A.view_as_data t with
      | T_cstor (cstor,args) ->
        Some {c_n=n;c_cstor=cstor; c_args=args}, []
      | _ -> None, []

    let merge cc n1 c1 n2 c2 e_n1_n2 : _ result =
      Log.debugf 5
        (fun k->k "(@[%s.merge@ (@[:c1 %a %a@])@ (@[:c2 %a %a@])@])"
            name N.pp n1 pp c1 N.pp n2 pp c2); 
      (* build full explanation of why the constructor terms are equal *)
      (* TODO: have a sort of lemma (injectivity) here to justify this in the proof *)
      let expl =
        Expl.mk_list [
          e_n1_n2;
          Expl.mk_merge n1 c1.c_n;
          Expl.mk_merge n2 c2.c_n;
        ]
      in
      if A.Cstor.equal c1.c_cstor c2.c_cstor then (
        (* same function: injectivity *)
        assert (IArray.length c1.c_args = IArray.length c2.c_args);
        IArray.iter2
          (fun u1 u2 -> SI.CC.merge_t cc u1 u2 expl)
          c1.c_args c2.c_args;
        Ok c1
      ) else (
        (* different function: disjointness *)
        Error expl
      )
  end

  (** Monoid mapping each class to the set of is-a/select of which it
      is the argument *)
  module Monoid_parents = struct
    module SI = SI
    let name = "th-data.parents"

    type select = {
      sel_n: N.t;
      sel_cstor: A.Cstor.t;
      sel_idx: int;
      sel_arg: T.t;
    }

    type is_a = {
      is_a_n: N.t;
      is_a_cstor: A.Cstor.t;
      is_a_arg: T.t;
    }

    (* associate to each class a unique constructor term in the class (if any) *)
    type t = {
      parent_is_a: is_a list;(* parents that are [is-a] *)
      parent_select: select list; (* parents that are [select] *)
    }

    let pp_select out s = Fmt.fprintf out "(@[sel[%d]-%a@ :n %a@])" s.sel_idx A.Cstor.pp s.sel_cstor N.pp s.sel_n
    let pp_is_a out s = Fmt.fprintf out "(@[is-%a@ :n %a@])" A.Cstor.pp s.is_a_cstor N.pp s.is_a_n
    let pp out (v:t) =
      Fmt.fprintf out
        "(@[%s@ @[:sel [@[%a@]]@]@ @[:is-a [@[%a@]]@]@])"
        name
        (Util.pp_list pp_select) v.parent_select
        (Util.pp_list pp_is_a) v.parent_is_a

    (* attach data to constructor terms *)
    let of_term n (t:T.t) : _ option * _ list =
      match A.view_as_data t with
      | T_select (c, i, u) ->
        let m_sel = {
          parent_select=[{sel_n=n; sel_idx=i; sel_cstor=c; sel_arg=u}];
          parent_is_a=[];
        } in
        None, [u, m_sel]
      | T_is_a (c, u) ->
        let m_sel = {
          parent_is_a=[{is_a_n=n; is_a_cstor=c; is_a_arg=u;}];
          parent_select=[];
        } in
        None, [u, m_sel]
      | T_cstor _ | T_other _ -> None, []

    let merge cc n1 v1 n2 v2 _e : _ result =
      Log.debugf 5
        (fun k->k "(@[%s.merge@ @[:c1 %a %a@]@ @[:c2 %a %a@]@])"
            name N.pp n1 pp v1 N.pp n2 pp v2); 
      let parent_is_a = v1.parent_is_a @ v2.parent_is_a in
      let parent_select = v1.parent_select @ v2.parent_select in
      Ok {parent_is_a; parent_select;}
  end

  module ST_cstors = Sidekick_core.Monoid_of_repr(Monoid_cstor)
  module ST_parents = Sidekick_core.Monoid_of_repr(Monoid_parents)
  module N_tbl = Backtrackable_tbl.Make(N)

  type t = {
    tst: T.state;
    cstors: ST_cstors.t; (* repr -> cstor for the class *)
    parents: ST_parents.t; (* repr -> parents for the class *)
    cards: Card.t; (* remember finiteness *)
    to_decide: unit N_tbl.t; (* set of terms to decide. *)
    case_split_done: unit T.Tbl.t; (* set of terms for which case split is done *)
    (* TODO: bitfield for types with less than 62 cstors, to quickly detect conflict? *)
  }

  let push_level self =
    ST_cstors.push_level self.cstors;
    ST_parents.push_level self.parents;
    N_tbl.push_level self.to_decide;
    ()

  let pop_levels self n =
    ST_cstors.pop_levels self.cstors n;
    ST_parents.pop_levels self.parents n;
    N_tbl.pop_levels self.to_decide n;
    ()

  (* TODO: select/is-a *)

  (* TODO: remove
  (* attach data to constructor terms *)
  let on_new_term_look_at_shape self n (t:T.t) =
    match A.view_as_data t with
    | T_cstor (cstor,args) ->
      Log.debugf 20
        (fun k->k "(@[%s.on-new-term@ %a@ :cstor %a@ @[:args@ (@[%a@])@]@]@])"
            name T.pp t A.Cstor.pp cstor (Util.pp_iarray T.pp) args);
      N_tbl.add self.cstors n {n; t; cstor; args};
    | T_select (cstor,i,u) ->
      Log.debugf 20
        (fun k->k "(@[%s.on-new-term.select[%d]@ %a@ :cstor %a@ :in %a@])"
            name i T.pp t A.Cstor.pp cstor T.pp u);
      (* TODO: remember that [u] must be decided *)
      ()
      (*       N_tbl.add self.cstors n {n; t; cstor; args}; *)
    | T_is_a (cstor,u) ->
      Log.debugf 20
        (fun k->k "(@[%s.on-new-term.is-a@ %a@ :cstor %a@ :in %a@])"
            name T.pp t A.Cstor.pp cstor T.pp u);
      ()
      (*       N_tbl.add self.cstors n {n; t; cstor; args}; *)
    | T_other _ -> ()
     *)

  (* remember terms of a datatype *)
  let on_new_term_look_at_ty (self:t) n (t:T.t) : unit =
    let ty = T.ty t in
    match A.as_datatype ty with
    | Ty_data _ ->
      Log.debugf 20
        (fun k->k "(@[%s.on-new-term.has-data-ty@ %a@ :ty %a@])"
            name T.pp t Ty.pp ty);
      if Card.is_finite self.cards ty && not (N_tbl.mem self.to_decide n) then (
        (* must decide this term *)
        Log.debugf 20
          (fun k->k "(@[%s.on-new-term.must-decide-finite-ty@ %a@])" name T.pp t);
        N_tbl.add self.to_decide n ();
      )
    | _ -> ()

  let on_new_term (self:t) cc (n:N.t) (t:T.t) : unit =
    on_new_term_look_at_ty self n t; (* might have to decide [t] *)
    match A.view_as_data t with
    | T_is_a (c_t, u) ->
      let n_u = SI.CC.add_term cc u in
      let repr_u = SI.CC.find cc n_u in
      begin match ST_cstors.get self.cstors repr_u with
        | None ->
          N_tbl.add self.to_decide repr_u (); (* needs to be decided *)
        | Some cstor ->
          let is_true = A.Cstor.equal cstor.c_cstor c_t in
          Log.debugf 5
            (fun k->k "(@[%s.on-new-term.is-a.reduce@ :t %a@ :to %B@ :n %a@ :sub-cstor %a@])"
                name T.pp t is_true N.pp n Monoid_cstor.pp cstor);
          SI.CC.merge cc n (SI.CC.n_bool cc is_true) (Expl.mk_merge n_u repr_u)
      end
    | T_select (c_t, i, u) ->
      let n_u = SI.CC.add_term cc u in
      let repr_u = SI.CC.find cc n_u in
      begin match ST_cstors.get self.cstors repr_u with
        | Some cstor when A.Cstor.equal cstor.c_cstor c_t ->
          Log.debugf 5
            (fun k->k "(@[%s.on-new-term.select.reduce@ :n %a@ :sel get[%d]-%a@])"
                name N.pp n i A.Cstor.pp c_t);
          assert (i < IArray.length cstor.c_args);
          let u_i = IArray.get cstor.c_args i in
          let n_u_i = SI.CC.add_term cc u_i in
          SI.CC.merge cc n n_u_i (Expl.mk_merge n_u repr_u)
        | Some _ -> ()
        | None ->
          N_tbl.add self.to_decide repr_u (); (* needs to be decided *)
      end
    | T_cstor _ | T_other _ -> ()

  let cstors_of_ty (ty:Ty.t) : A.Cstor.t Iter.t =
    match A.as_datatype ty with
    | Ty_data {cstors} -> cstors
    | _ -> assert false

  let on_pre_merge (self:t) (cc:SI.CC.t) acts n1 n2 expl : unit =
    let merge_is_a n1 (c1:Monoid_cstor.t) n2 (is_a2:Monoid_parents.is_a) =
      let is_true = A.Cstor.equal c1.c_cstor is_a2.is_a_cstor in
      Log.debugf 50
        (fun k->k "(@[%s.on-merge.is-a.reduce@ %a@ :to %B@ :n1 %a@ :n2 %a@ :sub-cstor %a@])"
            name Monoid_parents.pp_is_a is_a2 is_true N.pp n1 N.pp n2 Monoid_cstor.pp c1);
      SI.CC.merge cc is_a2.is_a_n (SI.CC.n_bool cc is_true)
        Expl.(mk_list [mk_merge n1 c1.c_n; mk_merge n1 n2;
                       mk_merge_t (N.term n2) is_a2.is_a_arg])
    in
    let merge_select n1 (c1:Monoid_cstor.t) n2 (sel2:Monoid_parents.select) =
      if A.Cstor.equal c1.c_cstor sel2.sel_cstor then (
        Log.debugf 5
          (fun k->k "(@[%s.on-merge.select.reduce@ :n2 %a@ :sel get[%d]-%a@])"
              name N.pp n2 sel2.sel_idx Monoid_cstor.pp c1);
        assert (sel2.sel_idx < IArray.length c1.c_args);
        let u_i = IArray.get c1.c_args sel2.sel_idx in
        let n_u_i = SI.CC.add_term cc u_i in
        SI.CC.merge cc sel2.sel_n n_u_i
          Expl.(mk_list [mk_merge n1 c1.c_n; mk_merge n1 n2;
                         mk_merge_t (N.term n2) sel2.sel_arg]);
      )
    in
    let merge_c_p n1 n2 =
      match ST_cstors.get self.cstors n1, ST_parents.get self.parents n2 with
      | None, _
      | _, None -> ()
      | Some c1, Some p2 ->
        Log.debugf 50
          (fun k->k "(@[<hv>%s.pre-merge@ (@[:n1 %a@ :c1 %a@])@ (@[:n2 %a@ :p2 %a@])@])"
              name N.pp n1 Monoid_cstor.pp c1 N.pp n2 Monoid_parents.pp p2);
        List.iter (fun is_a2 -> merge_is_a n1 c1 n2 is_a2) p2.parent_is_a;
        List.iter (fun s2 -> merge_select n1 c1 n2 s2) p2.parent_select;
    in
    merge_c_p n1 n2;
    merge_c_p n2 n1;
    ()

  module Acyclicity_ = struct
    type st = {
      n: N.t;
      mutable flag: flag;
      cstor: Monoid_cstor.t;
    }
    and parent_uplink = {
      parent: st;
      t_eq_n: T.t;
    }
    and flag =
      | New | Done
      | Current of parent_uplink option

    let pp_st out st =
      Fmt.fprintf out "(@[st :cstor %a@ :flag %s@])"
        Monoid_cstor.pp st.cstor
        (match st.flag with
         | New -> "new" | Done -> "done"
         | Current None -> "current-top" | Current _ -> "current(_)")

    let pp_parent out {parent; t_eq_n} =
      Fmt.fprintf out "(@[parent@ :n %a@ :by-eq-t %a@])"
        N.pp parent.n T.pp t_eq_n

    let check (self:t) (solver:SI.t) (acts:SI.actions) : unit =
      let module Tbl = CCHashtbl.Make(N) in
      let cc = SI.cc solver in
      let tbl : st Tbl.t = Tbl.create 32 in
      (* traverse [n] with state [st], possibly from an equality [n=t_eq_n] *)
      let rec traverse ?parent (n:N.t) (st:st) : unit =
        Log.debugf 50
          (fun k->k "(@[data.acycl.traverse %a@ :st %a@ :parent %a@])"
              N.pp n pp_st st (Fmt.Dump.option pp_parent) parent);
        match st.flag with
        | Done -> ()
        | New ->
          st.flag <- Current parent;
          traverse_sub n st;
          st.flag <- Done
        | Current _parent ->
          let parent = CCOpt.or_ ~else_:_parent parent in
          Log.debugf 20
            (fun k->k "(@[data.acycl.found-loop@ %a@ :st %a@ :parent %a@])"
                N.pp n pp_st st (Fmt.Dump.option pp_parent) parent);
          (* conflict, we found a loop! *)
          let rec mk_path acc n parent =
            Log.debugf 100
              (fun k->k "(@[data.acycl.mk-path %a %a@])" N.pp n pp_parent parent);
            let acc = Expl.mk_merge_t (N.term n) parent.t_eq_n :: acc in
            let acc = Expl.mk_merge parent.parent.n parent.parent.n :: acc in
            match parent.parent.flag with
            | Current (Some p') -> mk_path acc parent.parent.n p'
            | _ -> acc
          in
          let c0 = [Expl.mk_merge n st.n;] in
          let c = match parent with
            | None -> c0
            | Some parent -> mk_path c0 n parent
          in
          SI.CC.raise_conflict_from_expl cc acts (Expl.mk_list c)
      (* traverse constructor arguments *)
      and traverse_sub n st: unit =
        IArray.iter
          (fun sub_t ->
             let sub = SI.CC.find_t cc sub_t in
             match Tbl.get tbl sub with
             | None -> ()
             | Some st' ->
               let parent = {parent=st; t_eq_n=sub_t} in
               traverse ~parent sub st')
          st.cstor.Monoid_cstor.c_args;
      in
      begin
        (* populate tbl with [repr->cstor] *)
        ST_cstors.iter_all self.cstors
          (fun (n, cstor) ->
             assert (not @@ Tbl.mem tbl n);
             Tbl.add tbl n {cstor; n; flag=New});
        Tbl.iter (fun n st -> traverse n st) tbl;
      end
  end

  (* FIXME: when merging [(is _ C) t] with false, remove [C] from the available list *)
  let on_partial_check (self:t) (solver:SI.t) (acts:SI.actions) trail =
    let check_lit lit =
      let t = SI.Lit.term lit in
      match A.view_as_data t with
      | T_is_a (c, u) when SI.Lit.sign lit ->
        (* add [((_ is C) u) ==> u = C(sel-c-0 u, …, sel-c-k u)] *)
        let rhs =
          let args =
            A.Cstor.ty_args c
            |> Iter.mapi (fun i _ty -> A.mk_sel self.tst c i u)
            |> Iter.to_list |> IArray.of_list
          in
          A.mk_cstor self.tst c args
        in
        Log.debugf 50
          (fun k->k"(@[%s.assign-is-a@ :lhs %a@ :rhs %a@ :lit %a@])"
              name T.pp u  T.pp rhs SI.Lit.pp lit);
        SI.cc_merge_t solver acts u rhs (Expl.mk_lit lit)
      | _ -> ()
    in
    Iter.iter check_lit trail

  (* on final check, check acyclicity,
     then make sure we have done case split on all terms that
     need it. *)
  let on_final_check (self:t) (solver:SI.t) (acts:SI.actions) _trail =
    Acyclicity_.check self solver acts;
    let remaining_to_decide =
      N_tbl.to_iter self.to_decide
      |> Iter.map (fun (n,_) -> SI.cc_find solver n)
      |> Iter.filter
        (fun n ->
           not (ST_cstors.mem self.cstors n) &&
           not (T.Tbl.mem self.case_split_done (N.term n)))
      |> Iter.to_rev_list
    in
    begin match remaining_to_decide with
      | [] -> ()
      | l ->
        Log.debugf 10
          (fun k->k "(@[%s.final-check.must-decide@ %a@])" name (Util.pp_list N.pp) l);
        (* add clauses [∨_c is-c(t)] and [¬(is-a t) ∨ ¬(is-b t)] *)
        List.iter
          (fun n ->
             let t = N.term n in
             (* [t] might have been expanded already, in case of duplicates in [l] *)
             if not @@ T.Tbl.mem self.case_split_done t then (
               T.Tbl.add self.case_split_done t ();
               let c =
                 cstors_of_ty (T.ty t) 
                 |> Iter.map (fun c -> A.mk_is_a self.tst c t)
                 |> Iter.map
                   (fun t ->
                      let lit = SI.mk_lit solver acts t in
                      (* TODO: set default polarity, depending on n° of args? *)
                      lit)
                 |> Iter.to_rev_list
               in
               SI.add_clause_permanent solver acts c;
               Iter.diagonal_l c
                 (fun (c1,c2) ->
                    SI.add_clause_permanent solver acts
                      [SI.Lit.neg c1; SI.Lit.neg c2]);
             ))
          l
    end;
    ()

  let create_and_setup (solver:SI.t) : t =
    let self = {
      tst=SI.tst solver;
      cstors=ST_cstors.create_and_setup ~size:32 solver;
      parents=ST_parents.create_and_setup ~size:32 solver;
      to_decide=N_tbl.create ~size:16 ();
      case_split_done=T.Tbl.create 16;
      cards=Card.create();
    } in
    Log.debugf 1 (fun k->k "(setup :%s)" name);
    SI.on_cc_new_term solver (on_new_term self);
    SI.on_cc_pre_merge solver (on_pre_merge self);
    SI.on_partial_check solver (on_partial_check self);
    SI.on_final_check solver (on_final_check self);
    self

  let theory =
    A.S.mk_theory ~name ~push_level ~pop_levels ~create_and_setup ()
end

(*
module Datatype(A : Congruence_closure.THEORY_ACTION)
  : Congruence_closure.THEORY with module A=A = struct
  module A = A

  (* merge equiv classes:
     - injectivity rule on normal forms
     - check consistency of normal forms
     - intersection of label sets  *)
  let merge (ra:A.repr) (rb:A.repr) expls =
    begin match A.nf ra, A.nf rb with
      | Some (NF_cstor (c1, args1)), Some (NF_cstor (c2, args2)) ->
        if Cst.equal c1.cstor_cst c2.cstor_cst then (
          (* unify arguments recursively, by injectivity *)
          assert (IArray.length args1 = IArray.length args2);
          IArray.iter2
            (fun sub1 sub2 ->
               A.add_eqn sub1 sub2
                 (CC_injectivity (A.term_of_repr ra, A.term_of_repr rb)))
            args1 args2;
        ) else (
          A.unsat expls
        )
      | _ -> ()
    end;
    (* TODO: intersect label sets *)
    (* TODO: check if Split2 applies *)
    ()

  type map_status =
    | Map_empty
    | Map_single of data_cstor
    | Map_other

  type labels = data_cstor ID.Map.t

  (* check if set of cstors is empty or unary *)
  let map_status (m: labels): map_status =
    if ID.Map.is_empty m then Map_empty
    else (
      let c, cstor = ID.Map.choose m in
      let m' = ID.Map.remove c m in
      if ID.Map.is_empty m'
      then Map_single cstor
      else Map_other
    )

  (* propagate [r = cstor], using Instantiation rules *)
  let propagate_cstor (r:A.repr) (cstor:data_cstor) (expl:cc_explanation list): unit =
    Log.debugf 5
      (fun k->k "(@[propagate_cstor@ %a@ %a: expl: (@[%a@])@])"
          Term.pp (A.term_of_repr r) Cst.pp cstor.cstor_cst
          (Util.pp_list pp_cc_explanation) expl);
    (* TODO: propagate, add_eqn with cstor term, but only
       if either:
       - cstor is finite
       - or some parent term of [r_u] is a selector.

       We need to create new constants for the arguments *)
    assert false

  (* perform (Split 2) if all the cstors of [m] (labels of [r]) are finite
     and (Split 1) was not applied on [r] *)
  let maybe_split (r:A.repr) (m: labels) (expl:cc_explanation list): unit =
    assert (ID.Map.cardinal m >= 2);
    if ID.Map.for_all (fun _ cstor -> Cst.is_finite_cstor cstor.cstor_cst) m
    && not (Term_bits.get Term.field_is_split (A.term_of_repr r).term_bits)
    then (
      Log.debugf 5
        (fun k->k "(@[split_finite@ %a@ cstors: (@[<hv>%a@])@ expl: (@[%a@])@])"
            Term.pp (A.term_of_repr r) (Util.pp_list Cst.pp)
            (ID.Map.values m |> Sequence.map (fun c->c.cstor_cst) |> Sequence.to_list)
            (Util.pp_list pp_cc_explanation) expl);
      let lits =
        ID.Map.values m
        |> Sequence.map
          (fun cstor -> Lit.cstor_test cstor (A.term_of_repr r))
        |> Sequence.to_list
      in
      A.split lits expl
    )

  let set_nf t nf (e:cc_explanation): unit = match nf, t.term_cell with
    | NF_bool sign, App_cst ({cst_kind=Cst_test (_, lazy cstor); _}, args) ->
      (* update set of possible cstors for [A.find args.(0)]
         if [t = is-cstor args] is true/false *)
      assert (IArray.length args = 1);
      let u = IArray.get args 1 in
      let r_u = A.find u in
      let cstor_set, expl = match (A.term_of_repr r_u).term_cases_set with
        | TC_cstors (m,e') -> m,e'
        | _ -> assert false
      in
      let new_expl = e::expl in
      let cstor_id = cstor.cstor_cst.cst_id in
      if sign then (
        if ID.Map.mem cstor_id cstor_set then (
          (* unit propagate now *)
          propagate_cstor r_u cstor new_expl
        ) else (
          A.unsat new_expl (* conflict: *)
        )
      ) else (
        (* remove [cstor] from the set *)
        if ID.Map.mem cstor_id cstor_set then (
          Log.debugf 5
            (fun k->k "(@[remove_cstor@ %a@ from %a@])" ID.pp cstor_id Term.pp u);
          let new_set = ID.Map.remove cstor_id cstor_set in
          begin match map_status new_set with
            | Map_empty ->
              A.unsat new_expl (* conflict *)
            | Map_single cstor' ->
              propagate_cstor r_u cstor' new_expl;
            | Map_other ->
              (* just update set of labels *)
              if Backtrack.not_at_level_0 () then (
                let old_cases = (A.term_of_repr r_u).term_cases_set in
                Backtrack.push_undo (fun () -> (A.term_of_repr r_u).term_cases_set <- old_cases);
              );
              (A.term_of_repr r_u).term_cases_set <- TC_cstors (new_set, new_expl);
              maybe_split r_u new_set new_expl
          end
        )
      )
    | _ -> ()

  let eval t = match t.term_cell with
    | Case (u, m) ->
      let r_u = A.find u in
      begin match A.nf r_u with
        | Some (NF_cstor (c, _)) ->
          (* reduce to the proper branch *)
          let rhs =
            try ID.Map.find c.cstor_cst.cst_id m
            with Not_found -> assert false
          in
          A.add_eqn t rhs (CC_reduce_nf u);
        | Some (NF_bool _) -> assert false
        | None -> ()
      end
    | App_cst ({cst_kind=Cst_test(_,lazy cstor); _}, a) when IArray.length a=1 ->
      (* check if [a.(0)] has a constructor *)
      let arg = IArray.get a 0 in
      let r_a = A.find arg in
      begin match A.nf r_a with
        | None -> ()
        | Some (NF_cstor (cstor', _)) ->
          (* reduce to true/false depending on whether [cstor=cstor'] *)
          if Cst.equal cstor.cstor_cst cstor'.cstor_cst then (
            A.add_eqn t Term.true_ (CC_reduce_nf arg)
          ) else (
            A.add_eqn t Term.true_ (CC_reduce_nf arg)
          )
        | Some (NF_bool _) -> assert false
      end
    | App_cst ({cst_kind=Cst_proj(_,lazy cstor,i); _}, a) when IArray.length a=1 ->
      (* reduce if [a.(0)] has the proper constructor *)
      let arg = IArray.get a 0 in
      let r_a = A.find arg in
      begin match A.nf r_a with
        | None -> ()
        | Some (NF_cstor (cstor', nf_cstor_args)) ->
          (* [proj-C-i (C t1...tn) = ti] *)
          if Cst.equal cstor.cstor_cst cstor'.cstor_cst then (
            A.add_eqn t (IArray.get nf_cstor_args i) (CC_reduce_nf arg)
          )
        | Some (NF_bool _) -> assert false
      end
    | _ -> ()

  let is_evaluable t = match t.term_cell with
    | Case _ -> true
    | App_cst ({cst_kind=Cst_test(_,_); _}, a)
    | App_cst ({cst_kind=Cst_proj(_,_,_); _}, a) ->
      IArray.length a=1
    | _ -> false

  (* split every term that is not split yet, and to which some selectors
     are applied *)
  let split_rule () =
    let is_in_proj (r:A.repr): bool =
      Bag.to_seq (A.term_of_repr r).term_parents
      |> Sequence.exists
        (fun parent -> match parent.term_cell with
           | App_cst ({cst_kind=Cst_proj _; _}, a) ->
             let res = IArray.length a = 1 in
             (* invariant: a.(0) == r should hold *)
             if res then assert(A.equal_repr r (IArray.get a 1 |> A.find));
             res
           | _ -> false)
    in
    begin
      Log.debug 3 "(data.split1)";
      A.all_classes
      |> Sequence.filter
        (fun (r:A.repr) ->
           (* keep only terms of data-type, never split, with at least
              two possible cases in their label, and that occur in
              at least one selector *)
           Format.printf "check %a@." Term.pp (A.term_of_repr r);
           Ty.is_data (A.term_of_repr r).term_ty
           &&
           begin match (A.term_of_repr r).term_cases_set with
             | TC_cstors (m, _) -> ID.Map.cardinal m >= 2
             | _ -> assert false
           end
           &&
           not (Term_bits.get Term.field_is_split (A.term_of_repr r).term_bits)
           &&
           is_in_proj r)
      |> Sequence.iter
        (fun r ->
           let r = A.term_of_repr r in
           Log.debugf 5 (fun k->k "(@[split_1@ term: %a@])" Term.pp r);
           (* unconditional split: consider all cstors *)
           let cstors = match r.term_ty.ty_cell with
             | Atomic (_, Data {data_cstors=lazy cstors;_}) -> cstors
             | _ -> assert false
           in
           let lits =
             ID.Map.values cstors
             |> Sequence.map (fun cstor -> Lit.cstor_test cstor r)
             |> Sequence.to_list
           in
           r.term_bits <- Term_bits.set Term.field_is_split true r.term_bits;
           A.split lits [])
    end

  (* TODO acyclicity rule
     could be done by traversing the set of terms, assigning a "level" to
     each equiv class. If level clash, find why, return conflict.
  *)

  let final_check (): unit =
    split_rule ();
    (* TODO: acyclicity *)
    ()
end



      | Ast.Data l ->
        (* the datatypes in [l]. Used for computing cardinalities *)
        let in_same_block : ID.Set.t =
          List.map (fun {Ast.Ty.data_id; _} -> data_id) l |> ID.Set.of_list
        in
        (* declare the type, and all the constructors *)
        List.iter
          (fun {Ast.Ty.data_id; data_cstors} ->
             let ty = lazy (
               let card_ : ty_card ref = ref Finite in
               let cstors = lazy (
                 data_cstors
                 |> ID.Map.map
                   (fun c ->
                      let c_id = c.Ast.Ty.cstor_id in
                      let ty_c = conv_ty c.Ast.Ty.cstor_ty in
                      let ty_args, ty_ret = Ty.unfold ty_c in
                      (* add cardinality of [c] to the cardinality of [data_id].
                         (product of cardinalities of args) *)
                      let cstor_card =
                        ty_args
                        |> List.map
                          (fun ty_arg -> match ty_arg.ty_cell with
                             | Atomic (id, _) when ID.Set.mem id in_same_block ->
                               Infinite
                             | _ -> Lazy.force ty_arg.ty_card)
                        |> Ty_card.product
                      in
                      card_ := Ty_card.( !card_ + cstor_card );
                      let rec cst = lazy (
                        Cst.make_cstor c_id ty_c cstor
                      ) and cstor = lazy (
                        let cstor_proj = lazy (
                          let n = ref 0 in
                          List.map2
                            (fun id ty_arg ->
                               let ty_proj = Ty.arrow ty_ret ty_arg in
                               let i = !n in
                               incr n;
                               Cst.make_proj id ty_proj cstor i)
                            c.Ast.Ty.cstor_proj ty_args
                          |> IArray.of_list
                        ) in
                        let cstor_test = lazy (
                          let ty_test = Ty.arrow ty_ret Ty.prop in
                          Cst.make_tester c.Ast.Ty.cstor_test ty_test cstor
                        ) in
                        { cstor_ty=ty_c; cstor_cst=Lazy.force cst;
                          cstor_args=IArray.of_list ty_args;
                          cstor_proj; cstor_test; cstor_card; }
                      ) in
                      ID.Tbl.add decl_ty_ c_id cst; (* declare *)
                      Lazy.force cstor)
               )
               in
               let data = { data_cstors=cstors; } in
               let card = lazy (
                 ignore (Lazy.force cstors);
                 let r = !card_ in
                 Log.debugf 5
                   (fun k->k "(@[card_of@ %a@ %a@])" ID.pp data_id Ty_card.pp r);
                 r
               ) in
               Ty.atomic data_id (Data data) ~card
             ) in
             ID.Tbl.add ty_tbl_ data_id ty;
          )
          l;
        (* force evaluation *)
        List.iter
          (fun {Ast.Ty.data_id; _} ->
             let lazy ty = ID.Tbl.find ty_tbl_ data_id in
             ignore (Lazy.force ty.ty_card);
             begin match ty.ty_cell with
               | Atomic (_, Data {data_cstors=lazy _; _}) -> ()
               | _ -> assert false
             end)
          l
   *)
