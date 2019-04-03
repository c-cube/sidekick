
open Congruence_closure_intf

module type ARG = Congruence_closure_intf.ARG
module type S = Congruence_closure_intf.S

module Bits = CCBitField.Make()

let field_is_pending = Bits.mk_field()
(** true iff the node is in the [cc.pending] queue *)

let field_usr1 = Bits.mk_field()
(** General purpose *)

let field_usr2 = Bits.mk_field()
(** General purpose *)

let () = Bits.freeze()

module Make(A: ARG) = struct
  type term = A.Term.t
  type term_state = A.Term.state
  type lit = A.Lit.t
  type fun_ = A.Fun.t
  type proof = A.Proof.t
  type model = A.Model.t
  type th_data = A.Data.t

  (** Actions available to the theory *)
  type sat_actions = (Msat.void, lit, Msat.void, proof) Msat.acts

  module T = A.Term
  module Fun = A.Fun
  module Key = Key

  (** A node of the congruence closure.
      An equivalence class is represented by its "root" element,
      the representative. *)
  type node = {
    n_term: term;
    mutable n_sig0: signature option; (* initial signature *)
    mutable n_bits: Bits.t; (* bitfield for various properties *)
    mutable n_parents: node Bag.t; (* parent terms of this node *)
    mutable n_root: node; (* representative of congruence class (itself if a representative) *)
    mutable n_next: node; (* pointer to next element of congruence class *)
    mutable n_size: int; (* size of the class *)
    mutable n_as_lit: lit option; (* TODO: put into payload? and only in root? *)
    mutable n_expl: explanation_forest_link; (* the rooted forest for explanations *)
    mutable n_th_data: th_data; (* theory data *)
  }

  and signature = (fun_, node, node list) view

  and explanation_forest_link =
    | FL_none
    | FL_some of {
        next: node;
        expl: explanation;
      }

  (* atomic explanation in the congruence closure *)
  and explanation =
    | E_reduction (* by pure reduction, tautologically equal *)
    | E_lit of lit (* because of this literal *)
    | E_merge of node * node
    | E_merge_t of term * term
    | E_congruence of node * node (* caused by normal congruence *)
    | E_and of explanation * explanation

  type repr = node
  type conflict = lit list

  module N = struct
    type t = node

    let[@inline] equal (n1:t) n2 = n1 == n2
    let[@inline] hash n = T.hash n.n_term
    let[@inline] term n = n.n_term
    let[@inline] pp out n = T.pp out n.n_term
    let[@inline] as_lit n = n.n_as_lit
    let[@inline] th_data n = n.n_th_data

    let make (t:term) : t =
      let rec n = {
        n_term=t;
        n_sig0= None;
        n_bits=Bits.empty;
        n_parents=Bag.empty;
        n_as_lit=None; (* TODO: provide a method to do it *)
        n_root=n;
        n_expl=FL_none;
        n_next=n;
        n_size=1;
        n_th_data=A.Data.empty;
      } in
      n

    let[@inline] is_root (n:node) : bool = n.n_root == n

    (* traverse the equivalence class of [n] *)
    let iter_class_ (n:node) : node Iter.t =
      fun yield ->
        let rec aux u =
          yield u;
          if u.n_next != n then aux u.n_next
        in
        aux n

    let[@inline] iter_class n =
      assert (is_root n);
      iter_class_ n

    let[@inline] iter_parents (n:node) : node Iter.t =
      assert (is_root n);
      Bag.to_seq n.n_parents

    let[@inline] get_field f t = Bits.get f t.n_bits
    let[@inline] set_field f b t = t.n_bits <- Bits.set f b t.n_bits

    let[@inline] get_field_usr1 t = get_field field_usr1 t
    let[@inline] set_field_usr1 t b = set_field field_usr1 b t
    let[@inline] get_field_usr2 t = get_field field_usr2 t
    let[@inline] set_field_usr2 t b = set_field field_usr2 b t
  end

  module N_tbl = CCHashtbl.Make(N)

  module Expl = struct
    type t = explanation

    let rec pp out (e:explanation) = match e with
      | E_reduction -> Fmt.string out "reduction"
      | E_lit lit -> A.Lit.pp out lit
      | E_congruence (n1,n2) -> Fmt.fprintf out "(@[congruence@ %a@ %a@])" N.pp n1 N.pp n2
      | E_merge (a,b) -> Fmt.fprintf out "(@[merge@ %a@ %a@])" N.pp a N.pp b
      | E_merge_t (a,b) -> Fmt.fprintf out "(@[merge@ %a@ %a@])" T.pp a T.pp b
      | E_and (a,b) ->
        Format.fprintf out "(@[<hv1>and@ %a@ %a@])" pp a pp b

    let mk_reduction : t = E_reduction
    let[@inline] mk_congruence n1 n2 : t = E_congruence (n1,n2)
    let[@inline] mk_merge a b : t = if N.equal a b then mk_reduction else E_merge (a,b)
    let[@inline] mk_merge_t a b : t = if T.equal a b then mk_reduction else E_merge_t (a,b)
    let[@inline] mk_lit l : t = E_lit l

    let rec mk_list l =
      match l with
      | [] -> mk_reduction
      | [x] -> x
      | E_reduction :: tl -> mk_list tl
      | x :: y ->
        match mk_list y with
        | E_reduction -> x
        | y' -> E_and (x,y')
  end

  (** A signature is a shallow term shape where immediate subterms
      are representative *)
  module Signature = struct
    type t = signature
    let equal (s1:t) s2 : bool =
      match s1, s2 with
      | Bool b1, Bool b2 -> b1=b2
      | App_fun (f1,[]), App_fun (f2,[]) -> Fun.equal f1 f2
      | App_fun (f1,l1), App_fun (f2,l2) ->
        Fun.equal f1 f2 && CCList.equal N.equal l1 l2
      | App_ho (f1,l1), App_ho (f2,l2) ->
        N.equal f1 f2 && CCList.equal N.equal l1 l2
      | Not a, Not b -> N.equal a b
      | If (a1,b1,c1), If (a2,b2,c2) ->
        N.equal a1 a2 && N.equal b1 b2 && N.equal c1 c2
      | Eq (a1,b1), Eq (a2,b2) ->
        N.equal a1 a2 && N.equal b1 b2
      | Opaque u1, Opaque u2 -> N.equal u1 u2
      | Bool _, _ | App_fun _, _ | App_ho _, _ | If _, _
      | Eq _, _ | Opaque _, _ | Not _, _
        -> false

    let hash (s:t) : int =
      let module H = CCHash in
      match s with
      | Bool b -> H.combine2 10 (H.bool b)
      | App_fun (f, l) -> H.combine3 20 (Fun.hash f) (H.list N.hash l)
      | App_ho (f, l) -> H.combine3 30 (N.hash f) (H.list N.hash l)
      | Eq (a,b) -> H.combine3 40 (N.hash a) (N.hash b)
      | Opaque u -> H.combine2 50 (N.hash u)
      | If (a,b,c) -> H.combine4 60 (N.hash a)(N.hash b)(N.hash c)
      | Not u -> H.combine2 70 (N.hash u)

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list N.pp) l
      | App_ho (f, []) -> N.pp out f
      | App_ho (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" N.pp f (Util.pp_list N.pp) l
      | Opaque t -> N.pp out t
      | Not u -> Fmt.fprintf out "(@[not@ %a@])" N.pp u
      | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" N.pp a N.pp b
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" N.pp a N.pp b N.pp c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)
  module T_tbl = CCHashtbl.Make(T)

  type combine_task =
    | CT_merge of node * node * explanation

  type t = {
    tst: term_state;
    tbl: node T_tbl.t;
    (* internalization [term -> node] *)
    signatures_tbl : node Sig_tbl.t;
    (* map a signature to the corresponding node in some equivalence class.
       A signature is a [term_cell] in which every immediate subterm
       that participates in the congruence/evaluation relation
       is normalized (i.e. is its own representative).
       The critical property is that all members of an equivalence class
       that have the same "shape" (including head symbol)
       have the same signature *)
    pending: node Vec.t;
    combine: combine_task Vec.t;
    undo: (unit -> unit) Backtrack_stack.t;
    mutable on_merge: ev_on_merge list;
    mutable on_new_term: ev_on_new_term list;
    mutable ps_lits: lit list; (* TODO: thread it around instead? *)
    (* proof state *)
    ps_queue: (node*node) Vec.t;
    (* pairs to explain *)
    true_ : node lazy_t;
    false_ : node lazy_t;
    stat: Stat.t;
    count_conflict: int Stat.counter;
    count_merge: int Stat.counter;
  }
  (* TODO: an additional union-find to keep track, for each term,
     of the terms they are known to be equal to, according
     to the current explanation. That allows not to prove some equality
     several times.
     See "fast congruence closure and extensions", Nieuwenhis&al, page 14 *)

  and ev_on_merge = t -> N.t -> th_data -> N.t -> th_data -> Expl.t -> unit
  and ev_on_new_term = t -> N.t -> term -> th_data -> th_data option

  let[@inline] size_ (r:repr) = r.n_size
  let[@inline] true_ cc = Lazy.force cc.true_
  let[@inline] false_ cc = Lazy.force cc.false_
  let[@inline] term_state cc = cc.tst

  let[@inline] on_backtrack cc f : unit =
    Backtrack_stack.push_if_nonzero_level cc.undo f

  (* check if [t] is in the congruence closure.
     Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
  let[@inline] mem (cc:t) (t:term): bool = T_tbl.mem cc.tbl t

  (* find representative, recursively *)
  let[@unroll 2] rec find_rec (n:node) : repr =
    if n==n.n_root then (
      n
    ) else (
      let root = find_rec n.n_root in
      if root != n.n_root then (
        n.n_root <- root; (* path compression *)
      );
      root
    )

  (* non-recursive, inlinable function for [find] *)
  let[@inline] find_ (n:node) : repr =
    if n == n.n_root then n else find_rec n.n_root

  let[@inline] same_class (n1:node)(n2:node): bool =
    N.equal (find_ n1) (find_ n2)

  let[@inline] find _ n = find_ n

  (* print full state *)
  let pp_full out (cc:t) : unit =
    let pp_next out n =
      Fmt.fprintf out "@ :next %a" N.pp n.n_next in
    let pp_root out n =
      if N.is_root n then Fmt.string out " :is-root" else Fmt.fprintf out "@ :root %a" N.pp n.n_root in
    let pp_expl out n = match n.n_expl with
      | FL_none -> ()
      | FL_some e ->
        Fmt.fprintf out " (@[:forest %a :expl %a@])" N.pp e.next Expl.pp e.expl
    in
    let pp_n out n =
      Fmt.fprintf out "(@[%a%a%a%a@])" T.pp n.n_term pp_root n pp_next n pp_expl n
    and pp_sig_e out (s,n) =
      Fmt.fprintf out "(@[<1>%a@ ~~> %a%a@])" Signature.pp s N.pp n pp_root n
    in
    Fmt.fprintf out
      "(@[@{<yellow>cc.state@}@ (@[<hv>:nodes@ %a@])@ (@[<hv>:sig-tbl@ %a@])@])"
      (Util.pp_seq ~sep:" " pp_n) (T_tbl.values cc.tbl)
      (Util.pp_seq ~sep:" " pp_sig_e) (Sig_tbl.to_seq cc.signatures_tbl)

  (* compute up-to-date signature *)
  let update_sig (s:signature) : Signature.t =
    Congruence_closure_intf.map_view s
      ~f_f:(fun x->x)
      ~f_t:find_
      ~f_ts:(List.map find_)

  (* find whether the given (parent) term corresponds to some signature
     in [signatures_] *)
  let[@inline] find_signature cc (s:signature) : repr option =
    Sig_tbl.get cc.signatures_tbl s

  let add_signature cc (s:signature) (n:node) : unit =
    (* add, but only if not present already *)
    match Sig_tbl.find cc.signatures_tbl s with
    | exception Not_found ->
      Log.debugf 15
        (fun k->k "(@[cc.add-sig@ %a@ ~~> %a@])" Signature.pp s N.pp n);
      on_backtrack cc (fun () -> Sig_tbl.remove cc.signatures_tbl s);
      Sig_tbl.add cc.signatures_tbl s n;
    | r' ->
      assert (same_class n r');
      ()

  let push_pending cc t : unit =
    if not @@ N.get_field field_is_pending t then (
      Log.debugf 5 (fun k->k "(@[<hv1>cc.push_pending@ %a@])" N.pp t);
      N.set_field field_is_pending true t;
      Vec.push cc.pending t
    )

  let merge_classes cc t u e : unit =
    Log.debugf 5
      (fun k->k "(@[<hv1>cc.push_combine@ %a ~@ %a@ :expl %a@])"
        N.pp t N.pp u Expl.pp e);
    Vec.push cc.combine @@ CT_merge (t,u,e)

  (* re-root the explanation tree of the equivalence class of [n]
     so that it points to [n].
     postcondition: [n.n_expl = None] *)
  let rec reroot_expl (cc:t) (n:node): unit =
    let old_expl = n.n_expl in
    begin match old_expl with
      | FL_none -> () (* already root *)
      | FL_some {next=u; expl=e_n_u} ->
        reroot_expl cc u;
        u.n_expl <- FL_some {next=n; expl=e_n_u};
        n.n_expl <- FL_none;
    end

  let raise_conflict (cc:t) (acts:sat_actions) (e:conflict): _ =
    (* clear tasks queue *)
    Vec.iter (N.set_field field_is_pending false) cc.pending;
    Vec.clear cc.pending;
    Vec.clear cc.combine;
    let c = List.rev_map A.Lit.neg e in
    Stat.incr cc.count_conflict;
    acts.Msat.acts_raise_conflict c A.Proof.default

  let[@inline] all_classes cc : repr Iter.t =
    T_tbl.values cc.tbl
    |> Iter.filter N.is_root

  (* TODO: use markers and lockstep iteration instead *)
  (* distance from [t] to its root in the proof forest *)
  let[@inline][@unroll 2] rec distance_to_root (n:node): int = match n.n_expl with
    | FL_none -> 0
    | FL_some {next=t'; _} -> 1 + distance_to_root t'

  (* TODO: new bool flag on nodes +  stepwise progress + cleanup *)
  (* find the closest common ancestor of [a] and [b] in the proof forest *)
  let find_common_ancestor (a:node) (b:node) : node =
    let d_a = distance_to_root a in
    let d_b = distance_to_root b in
    (* drop [n] nodes in the path from [t] to its root *)
    let rec drop_ n t =
      if n=0 then t
      else match t.n_expl with
        | FL_none -> assert false
        | FL_some {next=t'; _} -> drop_ (n-1) t'
    in
    (* reduce to the problem where [a] and [b] have the same distance to root *)
    let a, b =
      if d_a > d_b then drop_ (d_a-d_b) a, b
      else if d_a < d_b then a, drop_ (d_b-d_a) b
      else a, b
    in
    (* traverse stepwise until a==b *)
    let rec aux_same_dist a b =
      if a==b then a
      else match a.n_expl, b.n_expl with
        | FL_none, _ | _, FL_none -> assert false
        | FL_some {next=a'; _}, FL_some {next=b'; _} -> aux_same_dist a' b'
    in
    aux_same_dist a b

  let[@inline] ps_add_obligation (cc:t) a b = Vec.push cc.ps_queue (a,b)
  let[@inline] ps_add_lit ps l = ps.ps_lits <- l :: ps.ps_lits

  let ps_clear (cc:t) =
    cc.ps_lits <- [];
    Vec.clear cc.ps_queue;
    ()

  (* decompose explanation [e] of why [n1 = n2] *)
  let rec decompose_explain cc (e:explanation) : unit =
    Log.debugf 5 (fun k->k "(@[cc.decompose_expl@ %a@])" Expl.pp e);
    match e with
    | E_reduction -> ()
    | E_congruence (n1, n2) ->
      begin match n1.n_sig0, n2.n_sig0 with
        | Some (App_fun (f1, a1)), Some (App_fun (f2, a2)) ->
          assert (Fun.equal f1 f2);
          assert (List.length a1 = List.length a2);
          List.iter2 (ps_add_obligation cc)  a1 a2;
        | Some (App_ho (f1, a1)), Some (App_ho (f2, a2)) ->
          assert (List.length a1 = List.length a2);
          ps_add_obligation cc f1 f2;
          List.iter2 (ps_add_obligation cc)  a1 a2;
        | Some (If (a1,b1,c1)), Some (If (a2,b2,c2)) ->
          ps_add_obligation cc a1 a2;
          ps_add_obligation cc b1 b2;
          ps_add_obligation cc c1 c2;
        | _ ->
          assert false
      end
    | E_lit lit -> ps_add_lit cc lit
    | E_merge (a,b) -> ps_add_obligation cc a b
    | E_merge_t (a,b) ->
      (* find nodes for [a] and [b] on the fly *)
      begin match T_tbl.find cc.tbl a, T_tbl.find cc.tbl b with
        | a, b -> ps_add_obligation cc a b
        | exception Not_found ->
          Error.errorf "expl: cannot find node(s) for %a, %a" T.pp a T.pp b
      end
    | E_and (a,b) -> decompose_explain cc a; decompose_explain cc b

  (* explain why [a = parent_a], where [a -> ... -> parent_a] in the
     proof forest *)
  let explain_along_path ps (a:node) (parent_a:node) : unit =
    let rec aux n =
      if n != parent_a then (
        match n.n_expl with
        | FL_none -> assert false
        | FL_some {next=next_n; expl=expl} ->
          decompose_explain ps expl;
          (* now prove [next_n = parent_a] *)
          aux next_n
      )
    in aux a

  (* find explanation *)
  let explain_loop (cc : t) : lit list =
    while not (Vec.is_empty cc.ps_queue) do
      let a, b = Vec.pop cc.ps_queue in
      Log.debugf 5
        (fun k->k "(@[cc.explain_loop.at@ %a@ =?= %a@])" N.pp a N.pp b);
      assert (N.equal (find_ a) (find_ b));
      let c = find_common_ancestor a b in
      explain_along_path cc a c;
      explain_along_path cc b c;
    done;
    cc.ps_lits

  let explain_eq_n ?(init=[]) cc (n1:node) (n2:node) : lit list =
    ps_clear cc;
    cc.ps_lits <- init;
    ps_add_obligation cc n1 n2;
    explain_loop cc

  let explain_unfold ?(init=[]) cc (e:explanation) : lit list =
    ps_clear cc;
    cc.ps_lits <- init;
    decompose_explain cc e;
    explain_loop cc

  (* add a term *)
  let [@inline] rec add_term_rec_ cc t : node =
    try T_tbl.find cc.tbl t
    with Not_found -> add_new_term_ cc t

  (* add [t] to [cc] when not present already *)
  and add_new_term_ cc (t:term) : node =
    assert (not @@ mem cc t);
    Log.debugf 15 (fun k->k "(@[cc.add-term@ %a@])" T.pp t);
    let n = N.make t in
    (* register sub-terms, add [t] to their parent list, and return the
       corresponding initial signature *)
    let sig0 = compute_sig0 cc n in
    n.n_sig0 <- sig0;
    (* remove term when we backtrack *)
    on_backtrack cc
      (fun () ->
         Log.debugf 15 (fun k->k "(@[cc.remove-term@ %a@])" T.pp t);
         T_tbl.remove cc.tbl t);
    (* add term to the table *)
    T_tbl.add cc.tbl t n;
    if CCOpt.is_some sig0 then (
      (* [n] might be merged with other equiv classes *)
      push_pending cc n;
    );
    (* initial theory data *)
    let th_data =
      List.fold_left
        (fun data f ->
           match f cc n t data with
           | None -> data
           | Some d -> d)
      A.Data.empty cc.on_new_term
    in
    n.n_th_data <- th_data;
    n

  (* compute the initial signature of the given node *)
  and compute_sig0 (self:t) (n:node) : Signature.t option =
    (* add sub-term to [cc], and register [n] to its parents *)
    let deref_sub (u:term) : node =
      let sub = add_term_rec_ self u in
      (* add [n] to [sub.root]'s parent list *)
      begin
        let sub = find_ sub in
        let old_parents = sub.n_parents in
        on_backtrack self (fun () -> sub.n_parents <- old_parents);
        sub.n_parents <- Bag.cons n sub.n_parents;
      end;
      sub
    in
    let[@inline] return x = Some x in
    match T.cc_view n.n_term with
    | Bool _ | Opaque _ -> None
    | Eq (a,b) ->
      let a = deref_sub a in
      let b = deref_sub b in
      return @@ Eq (a,b)
    | Not u -> return @@ Not (deref_sub u)
    | App_fun (f, args) ->
      let args = args |> Iter.map deref_sub |> Iter.to_list in
      if args<>[] then (
        return @@ App_fun (f, args)
      ) else None
    | App_ho (f, args) ->
      let args = args |> Iter.map deref_sub |> Iter.to_list in
      return @@ App_ho (deref_sub f, args)
    | If (a,b,c) ->
      return @@ If (deref_sub a, deref_sub b, deref_sub c)

  let[@inline] add_term cc t : node = add_term_rec_ cc t

  let set_as_lit cc (n:node) (lit:lit) : unit =
    match n.n_as_lit with
    | Some _ -> ()
    | None ->
      Log.debugf 15 (fun k->k "(@[cc.set-as-lit@ %a@ %a@])" N.pp n A.Lit.pp lit);
      on_backtrack cc (fun () -> n.n_as_lit <- None);
      n.n_as_lit <- Some lit

  let[@inline] n_is_bool (self:t) n : bool =
    N.equal n (true_ self) || N.equal n (false_ self)

  (* main CC algo: add terms from [pending] to the signature table,
     check for collisions *)
  let rec update_tasks (cc:t) (acts:sat_actions) : unit =
    while not (Vec.is_empty cc.pending && Vec.is_empty cc.combine) do
      while not @@ Vec.is_empty cc.pending do
        task_pending_ cc (Vec.pop cc.pending);
      done;
      while not @@ Vec.is_empty cc.combine do
        task_combine_ cc acts (Vec.pop cc.combine);
      done;
    done

  and task_pending_ cc (n:node) : unit =
    N.set_field field_is_pending false n;
    (* check if some parent collided *)
    begin match n.n_sig0 with
      | None -> () (* no-op *)
      | Some (Eq (a,b)) ->
        (* if [a=b] is now true, merge [(a=b)] and [true] *)
        if same_class a b then (
          let expl = Expl.mk_merge a b in
          merge_classes cc n (true_ cc) expl
        )
      | Some (Not u) ->
        (* [u = bool ==> not u = not bool] *)
        let r_u = find_ u in
        if N.equal r_u (true_ cc) then (
          let expl = Expl.mk_merge u (true_ cc) in
          merge_classes cc n (false_ cc) expl
        ) else if N.equal r_u (false_ cc) then (
          let expl = Expl.mk_merge u (false_ cc) in
          merge_classes cc n (true_ cc) expl
        )
      | Some s0 ->
        (* update the signature by using [find] on each sub-node *)
        let s = update_sig s0 in
        match find_signature cc s with
        | None ->
          (* add to the signature table [sig(n) --> n] *)
          add_signature cc s n
        | Some u when n == u -> ()
        | Some u ->
          (* [t1] and [t2] must be applications of the same symbol to
               arguments that are pairwise equal *)
          assert (n != u);
          let expl = Expl.mk_congruence n u in
          merge_classes cc n u expl
    end

  and[@inline] task_combine_ cc acts = function
    | CT_merge (a,b,e_ab) -> task_merge_ cc acts a b e_ab

  (* main CC algo: merge equivalence classes in [st.combine].
     @raise Exn_unsat if merge fails *)
  and task_merge_ cc acts a b e_ab : unit =
    let ra = find_ a in
    let rb = find_ b in
    if not @@ N.equal ra rb then (
      assert (N.is_root ra);
      assert (N.is_root rb);
      Stat.incr cc.count_merge;
      (* check we're not merging [true] and [false] *)
      if (N.equal ra (true_ cc) && N.equal rb (false_ cc)) ||
         (N.equal rb (true_ cc) && N.equal ra (false_ cc)) then (
        Log.debugf 5
          (fun k->k "(@[<hv>cc.merge.true_false_conflict@ @[:r1 %a@]@ @[:r2 %a@]@ :e_ab %a@])"
            N.pp ra N.pp rb Expl.pp e_ab);
        let lits = explain_unfold cc e_ab in
        let lits = explain_eq_n ~init:lits cc a ra in
        let lits = explain_eq_n ~init:lits cc b rb in
        raise_conflict cc acts lits
      );
      (* We will merge [r_from] into [r_into].
         we try to ensure that [size ra <= size rb] in general, but always
         keep values as representative *)
      let r_from, r_into =
        if n_is_bool cc ra then rb, ra
        else if n_is_bool cc rb then ra, rb
        else if size_ ra > size_ rb then rb, ra
        else ra, rb
      in
      (* when merging terms with [true] or [false], possibly propagate them to SAT *)
      let merge_bool r1 t1 r2 t2 =
        if N.equal r1 (true_ cc) then (
          propagate_bools cc acts r2 t2 r1 t1 e_ab true
        ) else if N.equal r1 (false_ cc) then (
          propagate_bools cc acts r2 t2 r1 t1 e_ab false
        )
      in
      merge_bool ra a rb b;
      merge_bool rb b ra a;
      (* perform [union r_from r_into] *)
      Log.debugf 15 (fun k->k "(@[cc.merge@ :from %a@ :into %a@])" N.pp r_from N.pp r_into);
      (* call [on_merge] functions, and merge theory data items *)
      begin
        let th_into = r_into.n_th_data in
        let th_from = r_from.n_th_data in
        let new_data = A.Data.merge th_into th_from in
        (* restore old data, if it changed *)
        if new_data != th_into then (
          on_backtrack cc (fun () -> r_into.n_th_data <- th_into);
        );
        r_into.n_th_data <- new_data;
        (* explanation is [a=ra & e_ab & b=rb] *)
        let expl = Expl.mk_list [e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb] in
        List.iter (fun f -> f cc r_into th_into r_from th_from expl) cc.on_merge;
      end;
      begin
        (* parents might have a different signature, check for collisions *)
        N.iter_parents r_from
          (fun parent -> push_pending cc parent);
        (* for each node in [r_from]'s class, make it point to [r_into] *)
        N.iter_class r_from
          (fun u ->
             assert (u.n_root == r_from);
             u.n_root <- r_into);
        (* now merge the classes *)
        let r_into_old_next = r_into.n_next in
        let r_from_old_next = r_from.n_next in
        let r_into_old_parents = r_into.n_parents in
        r_into.n_parents <- Bag.append r_into.n_parents r_from.n_parents;
        (* on backtrack, unmerge classes and restore the pointers to [r_from] *)
        on_backtrack cc
          (fun () ->
             Log.debugf 15
               (fun k->k "(@[cc.undo_merge@ :from %a :into %a@])"
                   N.pp r_from N.pp r_into);
             r_into.n_next <- r_into_old_next;
             r_from.n_next <- r_from_old_next;
             r_into.n_parents <- r_into_old_parents;
             N.iter_class_ r_from (fun u -> u.n_root <- r_from);
          );
        (* swap [into.next] and [from.next], merging the classes *)
        r_into.n_next <- r_from_old_next;
        r_from.n_next <- r_into_old_next;
      end;
      (* update explanations (a -> b), arbitrarily.
         Note that here we merge the classes by adding a bridge between [a]
         and [b], not their roots. *)
      begin
        reroot_expl cc a;
        assert (a.n_expl = FL_none);
        (* on backtracking, link may be inverted, but we delete the one
           that bridges between [a] and [b] *)
        on_backtrack cc
          (fun () -> match a.n_expl, b.n_expl with
             | FL_some e, _ when N.equal e.next b -> a.n_expl <- FL_none
             | _, FL_some e when N.equal e.next a -> b.n_expl <- FL_none
             | _ -> assert false);
        a.n_expl <- FL_some {next=b; expl=e_ab};
      end;
    )

  (* we are merging [r1] with [r2==Bool(sign)], so propagate each term [u1]
     in the equiv class of [r1] that is a known literal back to the SAT solver
     and which is not the one initially merged.
     We can explain the propagation with [u1 = t1 =e= t2 = r2==bool] *)
  and propagate_bools cc acts r1 t1 r2 t2 (e_12:explanation) sign : unit =
    (* explanation for [t1 =e= t2 = r2] *)
    let half_expl = lazy (
      let expl = explain_unfold cc e_12 in
      explain_eq_n ~init:expl cc r2 t2
    ) in
    (* TODO: flag per class, `or`-ed on merge, to indicate if the class
       contains at least one lit *)
    N.iter_class r1
      (fun u1 ->
         (* propagate if:
            - [u1] is a proper literal
            - [t2 != r2], because that can only happen
              after an explicit merge (no way to obtain that by propagation)
         *)
         match N.as_lit u1 with
         | Some lit when not (N.equal r2 t2) ->
           let lit = if sign then lit else A.Lit.neg lit in (* apply sign *)
           Log.debugf 5 (fun k->k "(@[cc.bool_propagate@ %a@])" A.Lit.pp lit);
           (* complete explanation with the [u1=t1] chunk *)
           let expl () =
             let e = explain_eq_n ~init:(Lazy.force half_expl) cc u1 t1 in
             e, A.Proof.default in
           let reason = Msat.Consequence expl in
           acts.Msat.acts_propagate lit reason
         | _ -> ())

  module Theory = struct
    type cc = t

    (* raise a conflict *)
    let raise_conflict cc expl =
      Log.debugf 5
        (fun k->k "(@[cc.theory.raise-conflict@ :expl %a@])" Expl.pp expl);
      merge_classes cc (true_ cc) (false_ cc) expl

    let merge cc n1 n2 expl =
      Log.debugf 5
        (fun k->k "(@[cc.theory.merge@ :n1 %a@ :n2 %a@ :expl %a@])" N.pp n1 N.pp n2 Expl.pp expl);
      merge_classes cc n1 n2 expl

    let add_term = add_term
  end

  let check_invariants_ (cc:t) =
    Log.debug 5 "(cc.check-invariants)";
    Log.debugf 15 (fun k-> k "%a" pp_full cc);
    assert (T.equal (T.bool cc.tst true) (true_ cc).n_term);
    assert (T.equal (T.bool cc.tst false) (false_ cc).n_term);
    assert (not @@ same_class (true_ cc) (false_ cc));
    assert (Vec.is_empty cc.combine);
    assert (Vec.is_empty cc.pending);
    (* check that subterms are internalized *)
    T_tbl.iter
      (fun t n ->
         assert (T.equal t n.n_term);
         assert (not @@ N.get_field field_is_pending n);
         assert (N.equal n.n_root n.n_next.n_root);
         (* check proper signature.
            note that some signatures in the sig table can be obsolete (they
            were not removed) but there must be a valid, up-to-date signature for
            each term *)
         begin match CCOpt.map update_sig n.n_sig0 with
           | None -> ()
           | Some s ->
             Log.debugf 15 (fun k->k "(@[cc.check-sig@ %a@ :sig %a@])" T.pp t Signature.pp s);
             (* add, but only if not present already *)
             begin match Sig_tbl.find cc.signatures_tbl s with
               | exception Not_found -> assert false
               | repr_s -> assert (same_class n repr_s)
             end
         end;
      )
      cc.tbl;
    ()

  let[@inline] check_invariants (cc:t) : unit =
    if Util._CHECK_INVARIANTS then check_invariants_ cc

  let add_seq cc seq =
    seq (fun t -> ignore @@ add_term_rec_ cc t);
    ()

  let[@inline] push_level (self:t) : unit =
    Backtrack_stack.push_level self.undo

  let pop_levels (self:t) n : unit =
    Vec.iter (N.set_field field_is_pending false) self.pending;
    Vec.clear self.pending;
    Vec.clear self.combine;
    Log.debugf 15
      (fun k->k "(@[cc.pop-levels %d@ :n-lvls %d@])" n (Backtrack_stack.n_levels self.undo));
    Backtrack_stack.pop_levels self.undo n ~f:(fun f -> f());
    ()

  (* assert that this boolean literal holds.
     if a lit is [= a b], merge [a] and [b];
     otherwise merge the atom with true/false *)
  let assert_lit cc lit : unit =
    let t = A.Lit.term lit in
    Log.debugf 5 (fun k->k "(@[cc.assert_lit@ %a@])" A.Lit.pp lit);
    let sign = A.Lit.sign lit in
    begin match T.cc_view t with
      | Eq (a,b) when sign ->
        let a = add_term cc a in
        let b = add_term cc b in
        (* merge [a] and [b] *)
        merge_classes cc a b (Expl.mk_lit lit)
      | _ ->
        (* equate t and true/false *)
        let rhs = if sign then true_ cc else false_ cc in
        let n = add_term cc t in
        (* TODO: ensure that this is O(1).
           basically, just have [n] point to true/false and thus acquire
           the corresponding value, so its superterms (like [ite]) can evaluate
           properly *)
        merge_classes cc n rhs (Expl.mk_lit lit)
    end

  let[@inline] assert_lits cc lits : unit =
    Iter.iter (assert_lit cc) lits

  let assert_eq cc t1 t2 (e:lit list) : unit =
    let expl = Expl.mk_list @@ List.rev_map Expl.mk_lit e in
    let n1 = add_term cc t1 in
    let n2 = add_term cc t2 in
    merge_classes cc n1 n2 expl

  let on_merge cc f = cc.on_merge <- f :: cc.on_merge
  let on_new_term cc f = cc.on_new_term <- f :: cc.on_new_term

  let create ?(stat=Stat.global)
      ?(on_merge=[]) ?(on_new_term=[]) ?(size=`Big) (tst:term_state) : t =
    let size = match size with `Small -> 128 | `Big -> 2048 in
    let rec cc = {
      tst;
      tbl = T_tbl.create size;
      signatures_tbl = Sig_tbl.create size;
      on_merge;
      on_new_term;
      pending=Vec.create();
      combine=Vec.create();
      ps_lits=[];
      undo=Backtrack_stack.create();
      ps_queue=Vec.create();
      true_;
      false_;
      stat;
      count_conflict=Stat.mk_int stat "cc.conflicts";
      count_merge=Stat.mk_int stat "cc.merges";
    } and true_ = lazy (
        add_term cc (T.bool tst true)
      ) and false_ = lazy (
        add_term cc (T.bool tst false)
      )
    in
    ignore (Lazy.force true_ : node);
    ignore (Lazy.force false_ : node);
    cc

  let[@inline] find_t cc t : repr =
    let n = T_tbl.find cc.tbl t in
    find_ n

  let[@inline] check cc acts : unit =
    Log.debug 5 "(cc.check)";
    update_tasks cc acts

  (* model: map each uninterpreted equiv class to some ID *)
  let mk_model (cc:t) (m:A.Model.t) : A.Model.t =
    let module Model = A.Model in
    let module Value = A.Value in
    Log.debugf 15 (fun k->k "(@[cc.mk-model@ %a@])" pp_full cc);
    let t_tbl = N_tbl.create 32 in
    (* populate [repr -> value] table *)
    T_tbl.values cc.tbl
      (fun r ->
         if N.is_root r then (
           (* find a value in the class, if any *)
           let v =
             N.iter_class r
             |> Iter.find_map (fun n -> Model.eval m n.n_term)
           in
           let v = match v with
             | Some v -> v
             | None ->
               if same_class r (true_ cc) then Value.true_
               else if same_class r (false_ cc) then Value.false_
               else Value.fresh r.n_term
           in
           N_tbl.add t_tbl r v
         ));
    (* now map every term to its representative's value *)
    let pairs =
      T_tbl.values cc.tbl
      |> Iter.map
        (fun n ->
           let r = find_ n in
           let v =
             try N_tbl.find t_tbl r
             with Not_found ->
               Error.errorf "didn't allocate a value for repr %a" N.pp r
           in
           n.n_term, v)
    in
    let m = Iter.fold (fun m (t,v) -> Model.add t v m) m pairs in
    Log.debugf 5 (fun k->k "(@[cc.model@ %a@])" Model.pp m);
    m
end
