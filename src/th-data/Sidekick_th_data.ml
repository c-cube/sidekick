
(** Theory for datatypes. *)

include Th_intf

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
  let to_string = function Finite -> "finite" | Infinite -> "infinite"
  let pp out self = Fmt.string out (to_string self)
end

(** Helper to compute the cardinality of types *)
module Compute_card(A : ARG) : sig
  type t
  val create : unit -> t
  val base_cstor : t -> A.S.T.Ty.t -> A.Cstor.t option
  val is_finite : t -> A.S.T.Ty.t -> bool
end = struct
  module Ty = A.S.T.Ty
  module Ty_tbl = CCHashtbl.Make(Ty)
  type ty_cell = {
    mutable card: C.t;
    mutable base_cstor: A.Cstor.t option;
  }
  type t = {
    cards: ty_cell Ty_tbl.t;
  }

  let create() : t = { cards=Ty_tbl.create 16}

  let find (self:t) (ty0:Ty.t) : ty_cell =
    let dr_tbl = Ty_tbl.create 16 in

    (* to build [ty], do we need to build [ty0]? *)
    let rec is_direct_recursion (ty:Ty.t) : bool =
      Ty.equal ty0 ty ||
      try Ty_tbl.find dr_tbl ty
      with Not_found ->
        Ty_tbl.add dr_tbl ty false; (* cut infinite loop *)
        let res =
          match A.as_datatype ty with
          | Ty_other -> false
          | Ty_arrow (_, ret) -> is_direct_recursion ret
          | Ty_app {args} -> Iter.exists is_direct_recursion args
          | Ty_data {cstors} ->
            Iter.flat_map A.Cstor.ty_args cstors
            |> Iter.exists is_direct_recursion
        in
        Ty_tbl.replace dr_tbl ty res;
        res
    in
    let is_direct_recursion_cstor (c:A.Cstor.t) : bool =
      Iter.exists is_direct_recursion (A.Cstor.ty_args c)
    in

    let rec get_cell (ty:Ty.t) : ty_cell =
      match Ty_tbl.find self.cards ty with
      | c -> c
      | exception Not_found ->
        (* insert temp value, for fixpoint computation *)
        let cell = {card=C.Infinite; base_cstor=None} in
        Ty_tbl.add self.cards ty cell;
        let card = match A.as_datatype ty with
          | Ty_other -> if A.ty_is_finite ty then C.Finite else C.Infinite
          | Ty_app {args} -> Iter.map get_card args |> C.product
          | Ty_arrow (args,ret) ->
            C.( (get_card ret) ^ (C.product @@ Iter.map get_card args))
          | Ty_data { cstors; } ->
            let c =
              cstors
              |> Iter.map
                (fun c ->
                   let card = C.product (Iter.map get_card @@ A.Cstor.ty_args c) in
                   (* we can use [c] as base constructor if it's finite,
                      or at least if it doesn't directly depend on [ty] in
                      its arguments *)
                   if card = C.Finite ||
                      (cell.base_cstor == None &&
                       not (is_direct_recursion_cstor c))
                   then (
                     cell.base_cstor <- Some c;
                   );
                   card)
              |> C.sum
            in
            A.ty_set_is_finite ty (c=Finite);
            assert (cell.base_cstor != None);
            c
        in
        cell.card <- card;
        Log.debugf 5
          (fun k->k "(@[th-data.card-ty@ %a@ :is %a@ :base-cstor %a@])"
              Ty.pp ty C.pp card (Fmt.Dump.option A.Cstor.pp) cell.base_cstor);
        cell
    and get_card ty = (get_cell ty).card
    in
    get_cell ty0

  let base_cstor self ty : A.Cstor.t option =
    let c = find self ty in
    c.base_cstor

  let is_finite self ty : bool =
    match (find self ty).card with
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
      c_args: N.t IArray.t;
    }

    let pp out (v:t) =
      Fmt.fprintf out "(@[%s@ :cstor %a@ :n %a@ :args [@[%a@]]@])"
        name A.Cstor.pp v.c_cstor N.pp v.c_n
        (Util.pp_iarray N.pp) v.c_args

    (* attach data to constructor terms *)
    let of_term cc n (t:T.t) : _ option * _ list =
      match A.view_as_data t with
      | T_cstor (cstor,args) ->
        let args = IArray.map (SI.CC.add_term cc) args in
        Some {c_n=n;c_cstor=cstor; c_args=args}, []
      | _ -> None, []

    let merge cc n1 c1 n2 c2 e_n1_n2 : _ result =
      Log.debugf 5
        (fun k->k "(@[%s.merge@ (@[:c1 %a@ %a@])@ (@[:c2 %a@ %a@])@])"
            name N.pp n1 pp c1 N.pp n2 pp c2);

      let mk_expl t1 t2 pr =
        Expl.mk_theory t1 t2 [
          N.term n1, N.term n2, [
            e_n1_n2;
            Expl.mk_merge n1 c1.c_n;
            Expl.mk_merge n2 c2.c_n;
          ]] pr
      in

      if A.Cstor.equal c1.c_cstor c2.c_cstor then (
        (* same function: injectivity *)

        let expl_merge i =
          let t1 = N.term c1.c_n in
          let t2 = N.term c2.c_n in
          mk_expl t1 t2 @@
          A.P.lemma_cstor_inj t1 t2 i (SI.CC.proof cc)
        in

        assert (IArray.length c1.c_args = IArray.length c2.c_args);
        IArray.iteri2
          (fun i u1 u2 -> SI.CC.merge cc u1 u2 (expl_merge i))
          c1.c_args c2.c_args;
        Ok c1
      ) else (
        (* different function: disjointness *)

        let expl =
          let t1 = N.term c1.c_n and t2 = N.term c2.c_n in
          mk_expl t1 t2 @@
          A.P.lemma_cstor_distinct t1 t2 (SI.CC.proof cc)
        in

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
      sel_arg: N.t;
    }

    type is_a = {
      is_a_n: N.t;
      is_a_cstor: A.Cstor.t;
      is_a_arg: N.t;
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
    let of_term cc n (t:T.t) : _ option * _ list =
      match A.view_as_data t with
      | T_select (c, i, u) ->
        let u = SI.CC.add_term cc u in
        let m_sel = {
          parent_select=[{sel_n=n; sel_idx=i; sel_cstor=c; sel_arg=u}];
          parent_is_a=[];
        } in
        None, [u, m_sel]
      | T_is_a (c, u) ->
        let u = SI.CC.add_term cc u in
        let m_sel = {
          parent_is_a=[{is_a_n=n; is_a_cstor=c; is_a_arg=u;}];
          parent_select=[];
        } in
        None, [u, m_sel]
      | T_cstor _ | T_other _ -> None, []

    let merge cc n1 v1 n2 v2 _e : _ result =
      Log.debugf 5
        (fun k->k "(@[%s.merge@ @[:c1 %a@ :v %a@]@ @[:c2 %a@ :v %a@]@])"
            name N.pp n1 pp v1 N.pp n2 pp v2);
      let parent_is_a = v1.parent_is_a @ v2.parent_is_a in
      let parent_select = v1.parent_select @ v2.parent_select in
      Ok {parent_is_a; parent_select;}
  end

  module ST_cstors = Sidekick_core.Monoid_of_repr(Monoid_cstor)
  module ST_parents = Sidekick_core.Monoid_of_repr(Monoid_parents)
  module N_tbl = Backtrackable_tbl.Make(N)

  type t = {
    tst: T.store;
    proof: SI.P.t;
    cstors: ST_cstors.t; (* repr -> cstor for the class *)
    parents: ST_parents.t; (* repr -> parents for the class *)
    cards: Card.t; (* remember finiteness *)
    to_decide: unit N_tbl.t; (* set of terms to decide. *)
    to_decide_for_complete_model: unit N_tbl.t; (* infinite types but we need a cstor in model*)
    case_split_done: unit T.Tbl.t; (* set of terms for which case split is done *)
    single_cstor_preproc_done: unit T.Tbl.t; (* preprocessed terms *)
    stat_acycl_conflict: int Stat.counter;
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

  let preprocess (self:t) si (acts:SI.preprocess_actions) (t:T.t) : _ option =
    let ty = T.ty t in
    match A.view_as_data t, A.as_datatype ty with
    | T_cstor _, _ -> None
    | _, Ty_data {cstors; _} ->
      begin match Iter.take 2 cstors |> Iter.to_rev_list with
        | [cstor] when not (T.Tbl.mem self.single_cstor_preproc_done t) ->
          (* single cstor: assert [t = cstor (sel-c-0 t, …, sel-c n t)] *)
          Log.debugf 50
            (fun k->k
                "(@[%s.preprocess.single-cstor@ %a@ :ty %a@ :cstor %a@])"
                name T.pp t Ty.pp ty A.Cstor.pp cstor);

          let (module Act) = acts in

          let u =
            let sel_args =
              A.Cstor.ty_args cstor
              |> Iter.mapi (fun i ty -> A.mk_sel self.tst cstor i t)
              |> Iter.to_array |> IArray.of_array_unsafe
            in
            A.mk_cstor self.tst cstor sel_args
          in

          (* proof: resolve [is-c(t) |- t = c(sel-c-0(t), …, sel-c-n(t))]
             with exhaustiveness: [|- is-c(t)] *)
          let proof =
            let pr_isa =
              A.P.lemma_isa_split t
                (Iter.return @@ Act.mk_lit_nopreproc (A.mk_is_a self.tst cstor t))
                self.proof
            and pr_eq_sel =
              A.P.lemma_select_cstor ~cstor_t:u t self.proof
            in
            SI.P.proof_r1 pr_isa pr_eq_sel self.proof
          in

          T.Tbl.add self.single_cstor_preproc_done t (); (* avoid loops *)
          T.Tbl.add self.case_split_done t (); (* no need to decide *)

          Act.add_clause [Act.mk_lit_nopreproc (A.mk_eq self.tst t u)] proof;
          None

        | _ -> None
      end
    | _ -> None

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
      ) else if not (N_tbl.mem self.to_decide n) &&
                not (N_tbl.mem self.to_decide_for_complete_model n) then (
        (* must pick a constructor for this term in order to build a model *)
        N_tbl.add self.to_decide_for_complete_model n ();
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
          let pr = A.P.lemma_isa_cstor ~cstor_t:(N.term cstor.c_n) t (SI.CC.proof cc) in
          let n_bool = SI.CC.n_bool cc is_true in
          SI.CC.merge cc n n_bool
            Expl.(mk_theory (N.term n) (N.term n_bool)
                    [N.term n_u, N.term cstor.c_n, [mk_merge n_u cstor.c_n]] pr)
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
          let pr = A.P.lemma_select_cstor ~cstor_t:(N.term cstor.c_n) t (SI.CC.proof cc) in
          SI.CC.merge cc n u_i
            Expl.(mk_theory (N.term n) (N.term u_i)
                    [N.term n_u, N.term cstor.c_n, [mk_merge n_u cstor.c_n]] pr)
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
      let pr =
        A.P.lemma_isa_cstor ~cstor_t:(N.term c1.c_n) (N.term is_a2.is_a_n) self.proof in
      let n_bool = SI.CC.n_bool cc is_true in
      SI.CC.merge cc is_a2.is_a_n n_bool
        (Expl.mk_theory (N.term is_a2.is_a_n) (N.term n_bool)
           [N.term n1, N.term n2,
            [Expl.mk_merge n1 c1.c_n; Expl.mk_merge n1 n2;
             Expl.mk_merge n2 is_a2.is_a_arg]] pr)
    in
    let merge_select n1 (c1:Monoid_cstor.t) n2 (sel2:Monoid_parents.select) =
      if A.Cstor.equal c1.c_cstor sel2.sel_cstor then (
        Log.debugf 5
          (fun k->k "(@[%s.on-merge.select.reduce@ :n2 %a@ :sel get[%d]-%a@])"
              name N.pp n2 sel2.sel_idx Monoid_cstor.pp c1);
        assert (sel2.sel_idx < IArray.length c1.c_args);
        let pr =
          A.P.lemma_select_cstor ~cstor_t:(N.term c1.c_n) (N.term sel2.sel_n) self.proof in
        let u_i = IArray.get c1.c_args sel2.sel_idx in
        SI.CC.merge cc sel2.sel_n u_i
          (Expl.mk_theory (N.term sel2.sel_n) (N.term u_i)
             [N.term n1, N.term n2,
              [Expl.mk_merge n1 c1.c_n; Expl.mk_merge n1 n2;
               Expl.mk_merge n2 sel2.sel_arg]] pr);
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
    type repr = N.t

    (* a node, corresponding to a class that has a constructor element. *)
    type node = {
      repr: N.t; (* repr *)
      cstor_n: N.t; (* the cstor node *)
      cstor_args: (N.t*repr) list; (* arguments to [cstor_n] *)
      mutable flag: flag;
    }
    and flag = New | Open | Done (* for cycle detection *)

    type graph = node N_tbl.t

    let pp_node out (n:node) =
      Fmt.fprintf out "(@[node@ :repr %a@ :cstor_n %a@ @[:cstor_args %a@]@])"
        N.pp n.repr N.pp n.cstor_n
        Fmt.(Dump.list @@ hvbox @@ pair ~sep:(return "@ --> ") N.pp N.pp) n.cstor_args
    let pp_path = Fmt.Dump.(list@@pair N.pp pp_node)
    let pp_graph out (g:graph) : unit =
      let pp_entry out (n,node) =
        Fmt.fprintf out "@[<1>@[graph_node[%a]@]@ := %a@]" N.pp n pp_node node
      in
      if N_tbl.length g = 0 then (
        Fmt.string out "(graph ø)"
      ) else (
        Fmt.fprintf out "(@[graph@ %a@])" (Fmt.iter pp_entry) (N_tbl.to_iter g)
      )

    let mk_graph (self:t) cc : graph =
      let g: graph = N_tbl.create ~size:32 () in
      let traverse_sub cstor : _ list =
        IArray.to_list_map
          (fun sub_n -> sub_n, SI.CC.find cc sub_n)
          cstor.Monoid_cstor.c_args
      in
      begin
        (* populate tbl with [repr->node] *)
        ST_cstors.iter_all self.cstors
          (fun (repr, cstor) ->
             assert (N.is_root repr);
             assert (not @@ N_tbl.mem g repr);
             let node = {
               repr; cstor_n=cstor.Monoid_cstor.c_n;
               cstor_args=traverse_sub cstor;
               flag=New;
             } in
             N_tbl.add g repr node);
      end;
      g

    let check (self:t) (solver:SI.t) (acts:SI.theory_actions) : unit =
      let cc = SI.cc solver in
      (* create graph *)
      let g = mk_graph self cc in
      Log.debugf 50
        (fun k->k"(@[%s.acyclicity.graph@ %a@])" name pp_graph g);
      (* traverse the graph, looking for cycles *)
      let rec traverse ~path (n:N.t) (r:repr) : unit =
        assert (N.is_root r);
        match N_tbl.find g r with
        | exception Not_found -> ()
        | {flag=Done; _} -> () (* no need *)
        | {flag=Open; cstor_n; _} as node ->
          (* conflict: the [path] forms a cycle *)
          let path = (n, node) :: path in
          let pr =
            A.P.lemma_acyclicity
              (Iter.of_list path |> Iter.map (fun (a,b) -> N.term a, N.term b.repr))
              self.proof
          in
          let expl =
            let subs =
              CCList.map
                (fun (n,node) ->
                   N.term n, N.term node.cstor_n,
                   [ Expl.mk_merge node.cstor_n node.repr;
                     Expl.mk_merge n node.repr;
                   ])
                path
            in
            Expl.mk_theory (N.term n) (N.term cstor_n) subs pr in
          Stat.incr self.stat_acycl_conflict;
          Log.debugf 5
            (fun k->k "(@[%s.acyclicity.raise_confl@ %a@ @[:path %a@]@])"
                name Expl.pp expl pp_path path);
          SI.CC.raise_conflict_from_expl cc acts expl
        | {flag=New; _} as node_r ->
          node_r.flag <- Open;
          let path = (n, node_r) :: path in
          List.iter (fun (sub_n,sub_r) -> traverse ~path sub_n sub_r) node_r.cstor_args;
          node_r.flag <- Done;
      in
      N_tbl.iter (fun r _ -> traverse ~path:[] r r) g;
      ()
  end

  let check_is_a self solver acts trail =
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
        let pr = A.P.lemma_isa_sel t self.proof in
        SI.cc_merge_t solver acts u rhs
          (Expl.mk_theory u rhs
             [t, N.term (SI.CC.n_true @@ SI.cc solver), [Expl.mk_lit lit]] pr)
      | _ -> ()
    in
    Iter.iter check_lit trail

  (* add clauses [\Or_c is-c(n)] and [¬(is-a n) ∨ ¬(is-b n)] *)
  let decide_class_ (self:t) (solver:SI.t) acts (n:N.t) : unit =
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
      SI.add_clause_permanent solver acts c
        (A.P.lemma_isa_split t (Iter.of_list c) self.proof);
      Iter.diagonal_l c
        (fun (l1,l2) ->
           let pr =
             A.P.lemma_isa_disj (SI.Lit.neg l1) (SI.Lit.neg l2) self.proof in
           SI.add_clause_permanent solver acts
             [SI.Lit.neg l1; SI.Lit.neg l2] pr);
    )

  (* on final check, check acyclicity,
     then make sure we have done case split on all terms that
     need it. *)
  let on_final_check (self:t) (solver:SI.t) (acts:SI.theory_actions) trail =
    Profile.with_ "data.final-check" @@ fun () ->
    check_is_a self solver acts trail;

    (* acyclicity check first *)
    Acyclicity_.check self solver acts;

    (* see if some classes that need a cstor have been case-split on already *)
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
      | [] ->
        Log.debugf 10
          (fun k->k "(@[%s.final-check.all-decided@ :cstors %a@ :parents %a@])"
              name ST_cstors.pp self.cstors ST_parents.pp self.parents);
        ()
      | l ->
        Log.debugf 10
          (fun k->k "(@[%s.final-check.must-decide@ %a@])" name (Util.pp_list N.pp) l);
        Profile.instant "data.case-split";
        List.iter (decide_class_ self solver acts) l
    end;

    if remaining_to_decide = [] then (
      let next_decision =
        N_tbl.to_iter self.to_decide_for_complete_model
        |> Iter.map (fun (n,_) -> SI.cc_find solver n)
        |> Iter.filter
          (fun n -> not (T.Tbl.mem self.case_split_done (N.term n))
                    && not (ST_cstors.mem self.cstors n))
        |> Iter.head
      in
      match next_decision with
      | None -> () (* all decided *)
      | Some n ->
        let t = N.term n in

        Profile.instant "data.decide";

        (* use a constructor that will not lead to an infinite loop *)
        let base_cstor =
          match Card.base_cstor self.cards (T.ty t) with
          | None -> Error.errorf "th-data:@ %a should have base cstor" N.pp n
          | Some c -> c
        in
        let cstor_app =
          let args =
            A.Cstor.ty_args base_cstor
            |> Iter.mapi (fun i _ -> A.mk_sel self.tst base_cstor i t)
            |> IArray.of_iter
          in
          A.mk_cstor self.tst base_cstor args
        in
        let t_eq_cstor = A.mk_eq self.tst t cstor_app in
        Log.debugf 20
          (fun k->k "(@[th-data.final-check.model.decide-cstor@ %a@])" T.pp t_eq_cstor);
        let lit = SI.mk_lit solver acts t_eq_cstor in
        SI.push_decision solver acts lit;
    );
    ()

  let on_model_gen (self:t) ~recurse (si:SI.t) (n:N.t) : T.t option =
    (* TODO: option to complete model or not (by picking sth at leaves)? *)
    let cc = SI.cc si in
    let repr = SI.CC.find cc n in
    match ST_cstors.get self.cstors repr with
    | None -> None
    | Some c ->
      Log.debugf 20 (fun k->k "(@[th-data.mk-model.find-cstor@ %a@])" Monoid_cstor.pp c);
      let args = IArray.map (recurse si) c.c_args in
      let t = A.mk_cstor self.tst c.c_cstor args in
      Some t

  let create_and_setup (solver:SI.t) : t =
    let self = {
      tst=SI.tst solver;
      proof=SI.proof solver;
      cstors=ST_cstors.create_and_setup ~size:32 solver;
      parents=ST_parents.create_and_setup ~size:32 solver;
      to_decide=N_tbl.create ~size:16 ();
      to_decide_for_complete_model=N_tbl.create ~size:16 ();
      single_cstor_preproc_done=T.Tbl.create 8;
      case_split_done=T.Tbl.create 16;
      cards=Card.create();
      stat_acycl_conflict=Stat.mk_int (SI.stats solver) "data.acycl.conflict";
    } in
    Log.debugf 1 (fun k->k "(setup :%s)" name);
    SI.on_preprocess solver (preprocess self);
    SI.on_cc_new_term solver (on_new_term self);
    SI.on_cc_pre_merge solver (on_pre_merge self);
    SI.on_final_check solver (on_final_check self);
    SI.on_model solver ~ask:(on_model_gen self);
    self

  let theory =
    A.S.mk_theory ~name ~push_level ~pop_levels ~create_and_setup ()
end
