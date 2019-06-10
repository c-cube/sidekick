module View = Sidekick_core.CC_view

type ('f, 't, 'ts) view = ('f, 't, 'ts) View.t =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 'ts
  | If of 't * 't * 't
  | Eq of 't * 't
  | Not of 't
  | Opaque of 't (* do not enter *)

module type ARG = Sidekick_core.CC_ARG
module type S = Sidekick_core.CC_S

module Make(CC_A: ARG) = struct
  module CC_A = CC_A
  module A = CC_A.A
  type term = A.Term.t
  type term_state = A.Term.state
  type lit = CC_A.Lit.t
  type fun_ = A.Fun.t
  type proof = A.Proof.t
  type actions = CC_A.Actions.t

  module T = A.Term
  module Fun = A.Fun
  module Lit = CC_A.Lit

  module Bits : sig
    type t = private int
    type field
    val empty : t
    val equal : t -> t -> bool
    val mk_field : unit -> field
    val get : field -> t -> bool
    val set : field -> bool -> t -> t
    val merge : t -> t -> t
  end = struct
    let max_width = Sys.word_size - 2
    let width = ref 0
    type t = int
    type field = int
    let empty : t = 0
    let mk_field () : field =
      let n = !width in
      if n > max_width then Error.errorf "maximum number of CC bitfields reached";
      incr width;
      n
    let[@inline] get field x = (x land field) <> 0
    let[@inline] set field b x =
      if b then x lor field else x land (lnot field)
    let merge = (lor)
    let equal : t -> t -> bool = Pervasives.(=)
  end

  let field_is_pending = Bits.mk_field()
  (** true iff the node is in the [cc.pending] queue *)

  let field_marked_explain = Bits.mk_field()
  (** used to mark traversed nodes when looking for a common ancestor *)

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

  module N = struct
    type t = node

    let[@inline] equal (n1:t) n2 = n1 == n2
    let[@inline] hash n = T.hash n.n_term
    let[@inline] term n = n.n_term
    let[@inline] pp out n = T.pp out n.n_term
    let[@inline] as_lit n = n.n_as_lit

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

    type bitfield = Bits.field
    let allocate_bitfield = Bits.mk_field
    let[@inline] get_field f t = Bits.get f t.n_bits
    let[@inline] set_field f b t = t.n_bits <- Bits.set f b t.n_bits
  end

  module N_tbl = CCHashtbl.Make(N)

  module Expl = struct
    type t = explanation

    let rec pp out (e:explanation) = match e with
      | E_reduction -> Fmt.string out "reduction"
      | E_lit lit -> Lit.pp out lit
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
    mutable on_conflict: ev_on_conflict list;
    mutable on_propagate: ev_on_propagate list;
    (* pairs to explain *)
    true_ : node lazy_t;
    false_ : node lazy_t;
    stat: Stat.t;
    count_conflict: int Stat.counter;
    count_props: int Stat.counter;
    count_merge: int Stat.counter;
  }
  (* TODO: an additional union-find to keep track, for each term,
     of the terms they are known to be equal to, according
     to the current explanation. That allows not to prove some equality
     several times.
     See "fast congruence closure and extensions", Nieuwenhis&al, page 14 *)

  and ev_on_merge = t -> actions -> N.t -> N.t -> Expl.t -> unit
  and ev_on_new_term = t -> N.t -> term -> unit
  and ev_on_conflict = t -> lit list -> unit
  and ev_on_propagate = t -> lit -> (unit -> lit list) -> unit

  let[@inline] size_ (r:repr) = r.n_size
  let[@inline] true_ cc = Lazy.force cc.true_
  let[@inline] false_ cc = Lazy.force cc.false_
  let[@inline] term_state cc = cc.tst

  let[@inline] on_backtrack cc f : unit =
    Backtrack_stack.push_if_nonzero_level cc.undo f

  (* check if [t] is in the congruence closure.
     Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
  let[@inline] mem (cc:t) (t:term): bool = T_tbl.mem cc.tbl t

  (* non-recursive, inlinable function for [find] *)
  let[@inline] find_ (n:node) : repr =
    let n2 = n.n_root in
    assert (N.is_root n2);
    n2

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
    View.map_view s
      ~f_f:(fun x->x)
      ~f_t:find_
      ~f_ts:(List.map find_)

  (* find whether the given (parent) term corresponds to some signature
     in [signatures_] *)
  let[@inline] find_signature cc (s:signature) : repr option =
    Sig_tbl.get cc.signatures_tbl s

  (* add to signature table. Assume it's not present already *)
  let add_signature cc (s:signature) (n:node) : unit =
    assert (not @@ Sig_tbl.mem cc.signatures_tbl s);
    Log.debugf 15
      (fun k->k "(@[cc.add-sig@ %a@ ~~> %a@])" Signature.pp s N.pp n);
    on_backtrack cc (fun () -> Sig_tbl.remove cc.signatures_tbl s);
    Sig_tbl.add cc.signatures_tbl s n

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
  let[@unroll 2] rec reroot_expl (cc:t) (n:node): unit =
    begin match n.n_expl with
      | FL_none -> () (* already root *)
      | FL_some {next=u; expl=e_n_u} ->
        (* reroot to [u], then invert link between [u] and [n] *)
        reroot_expl cc u;
        u.n_expl <- FL_some {next=n; expl=e_n_u};
        n.n_expl <- FL_none;
    end

  let raise_conflict (cc:t) (acts:actions) (e:lit list) : _ =
    (* clear tasks queue *)
    Vec.iter (N.set_field field_is_pending false) cc.pending;
    Vec.clear cc.pending;
    Vec.clear cc.combine;
    List.iter (fun f -> f cc e) cc.on_conflict;
    Stat.incr cc.count_conflict;
    CC_A.Actions.raise_conflict acts e A.Proof.default

  let[@inline] all_classes cc : repr Iter.t =
    T_tbl.values cc.tbl
    |> Iter.filter N.is_root

  (* find the closest common ancestor of [a] and [b] in the proof forest.

     Precond:
     - [a] and [b] are in the same class
     - no node has the flag [field_marked_explain] on
     Invariants:
     - if [n] is marked, then all the predecessors of [n]
       from [a] or [b] are marked too.
  *)
  let find_common_ancestor (a:node) (b:node) : node =
    (* catch up to the other node *)
    let rec find1 a =
      if N.get_field field_marked_explain a then a
      else (
        match a.n_expl with
        | FL_none -> assert false
        | FL_some r -> find1 r.next
      )
    in
    let rec find2 a b =
      if N.equal a b then a
      else if N.get_field field_marked_explain a then a
      else if N.get_field field_marked_explain b then b
      else (
        N.set_field field_marked_explain true a;
        N.set_field field_marked_explain true b;
        match a.n_expl, b.n_expl with
        | FL_some r1, FL_some r2 -> find2 r1.next r2.next
        | FL_some r, FL_none -> find1 r.next
        | FL_none, FL_some r -> find1 r.next
        | FL_none, FL_none -> assert false (* no common ancestor *)
      )

    in
    (* cleanup tags on nodes traversed in [find2] *)
    let rec cleanup_ n =
      if N.get_field field_marked_explain n then (
        N.set_field field_marked_explain false n;
        match n.n_expl with
        | FL_none -> ()
        | FL_some {next;_} -> cleanup_ next;
      )
    in
    let n = find2 a b in
    cleanup_ a;
    cleanup_ b;
    n

  (* decompose explanation [e] into a list of literals added to [acc] *)
  let rec explain_decompose cc (acc:lit list) (e:explanation) : _ list =
    Log.debugf 5 (fun k->k "(@[cc.decompose_expl@ %a@])" Expl.pp e);
    match e with
    | E_reduction -> acc
    | E_congruence (n1, n2) ->
      begin match n1.n_sig0, n2.n_sig0 with
        | Some (App_fun (f1, a1)), Some (App_fun (f2, a2)) ->
          assert (Fun.equal f1 f2);
          assert (List.length a1 = List.length a2);
          List.fold_left2 (explain_pair cc) acc a1 a2
        | Some (App_ho (f1, a1)), Some (App_ho (f2, a2)) ->
          assert (List.length a1 = List.length a2);
          let acc = explain_pair cc acc f1 f2 in
          List.fold_left2 (explain_pair cc) acc a1 a2
        | Some (If (a1,b1,c1)), Some (If (a2,b2,c2)) ->
          let acc = explain_pair cc acc a1 a2 in
          let acc = explain_pair cc acc b1 b2 in
          explain_pair cc acc c1 c2
        | _ ->
          assert false
      end
    | E_lit lit -> lit :: acc
    | E_merge (a,b) -> explain_pair cc acc a b
    | E_merge_t (a,b) ->
      (* find nodes for [a] and [b] on the fly *)
      begin match T_tbl.find cc.tbl a, T_tbl.find cc.tbl b with
        | a, b -> explain_pair cc acc a b
        | exception Not_found ->
          Error.errorf "expl: cannot find node(s) for %a, %a" T.pp a T.pp b
      end
    | E_and (a,b) ->
      let acc = explain_decompose cc acc a in
      explain_decompose cc acc b

  and explain_pair (cc:t) (acc:lit list) (a:node) (b:node) : _ list =
    Log.debugf 5
      (fun k->k "(@[cc.explain_loop.at@ %a@ =?= %a@])" N.pp a N.pp b);
    assert (N.equal (find_ a) (find_ b));
    let ancestor = find_common_ancestor a b in
    let acc = explain_along_path cc acc a ancestor in
    explain_along_path cc acc b ancestor

  (* explain why [a = parent_a], where [a -> ... -> target] in the
     proof forest *)
  and explain_along_path cc acc (a:node) (target:node) : _ list =
    let rec aux acc n =
      if n == target then acc
      else (
        match n.n_expl with
        | FL_none -> assert false
        | FL_some {next=next_n; expl=expl} ->
          let acc = explain_decompose cc acc expl in
          (* now prove [next_n = target] *)
          aux acc next_n
      )
    in aux acc a

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
    List.iter (fun f -> f cc n t) cc.on_new_term;
    n

  (* compute the initial signature of the given node *)
  and compute_sig0 (self:t) (n:node) : Signature.t option =
    (* add sub-term to [cc], and register [n] to its parents.
       Note that we return the exact sub-term, to get proper
       explanations, but we add to the sub-term's root's parent list. *)
    let deref_sub (u:term) : node =
      let sub = add_term_rec_ self u in
      (* add [n] to [sub.root]'s parent list *)
      begin
        let sub_r = find_ sub in
        let old_parents = sub_r.n_parents in
        on_backtrack self (fun () -> sub_r.n_parents <- old_parents);
        sub_r.n_parents <- Bag.cons n sub_r.n_parents;
      end;
      sub
    in
    let[@inline] return x = Some x in
    match CC_A.cc_view n.n_term with
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
      Log.debugf 15 (fun k->k "(@[cc.set-as-lit@ %a@ %a@])" N.pp n Lit.pp lit);
      on_backtrack cc (fun () -> n.n_as_lit <- None);
      n.n_as_lit <- Some lit

  let n_is_bool (self:t) n : bool =
    N.equal n (true_ self) || N.equal n (false_ self)

  (* main CC algo: add terms from [pending] to the signature table,
     check for collisions *)
  let rec update_tasks (cc:t) (acts:actions) : unit =
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
          Log.debugf 5 
            (fun k->k "(pending.eq@ %a@ :r1 %a@ :r2 %a@])" N.pp n N.pp a N.pp b);
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
        | Some u when N.equal n u -> ()
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
          (fun k->k "(@[<hv>cc.merge.true_false_conflict@ \
                     @[:r1 %a@ :t1 %a@]@ @[:r2 %a@ :t2 %a@]@ :e_ab %a@])"
            N.pp ra N.pp a N.pp rb N.pp b Expl.pp e_ab);
        let lits = explain_decompose cc [] e_ab in
        let lits = explain_pair cc lits a ra in
        let lits = explain_pair cc lits b rb in
        raise_conflict cc acts (List.rev_map Lit.neg lits)
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
        (* explanation is [a=ra & e_ab & b=rb] *)
        let expl = Expl.mk_list [e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb] in
        List.iter (fun f -> f cc acts r_into r_from expl) cc.on_merge;
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
        (* capture current state *)
        let r_into_old_next = r_into.n_next in
        let r_from_old_next = r_from.n_next in
        let r_into_old_parents = r_into.n_parents in
        let r_into_old_bits = r_into.n_bits in
        (* swap [into.next] and [from.next], merging the classes *)
        r_into.n_next <- r_from_old_next;
        r_from.n_next <- r_into_old_next;
        r_into.n_parents <- Bag.append r_into.n_parents r_from.n_parents;
        r_into.n_size <- r_into.n_size + r_from.n_size;
        r_into.n_bits <- Bits.merge r_into.n_bits r_from.n_bits;
        (* on backtrack, unmerge classes and restore the pointers to [r_from] *)
        on_backtrack cc
          (fun () ->
             Log.debugf 15
               (fun k->k "(@[cc.undo_merge@ :from %a :into %a@])"
                   N.pp r_from N.pp r_into);
             r_into.n_bits <- r_into_old_bits;
             r_into.n_next <- r_into_old_next;
             r_from.n_next <- r_from_old_next;
             r_into.n_parents <- r_into_old_parents;
             (* NOTE: this must come after the restoration of [next] pointers,
                otherwise we'd iterate on too big a class *)
             N.iter_class_ r_from (fun u -> u.n_root <- r_from);
             r_into.n_size <- r_into.n_size - r_from.n_size;
          );
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
      let lits = explain_decompose cc [] e_12 in
      explain_pair cc lits r2 t2
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
           let lit = if sign then lit else Lit.neg lit in (* apply sign *)
           Log.debugf 5 (fun k->k "(@[cc.bool_propagate@ %a@])" Lit.pp lit);
           (* complete explanation with the [u1=t1] chunk *)
           let reason =
             let e = lazy (explain_pair cc (Lazy.force half_expl) u1 t1) in
             fun () -> Lazy.force e
           in
           List.iter (fun f -> f cc lit reason) cc.on_propagate;
           Stat.incr cc.count_props;
           CC_A.Actions.propagate acts lit ~reason CC_A.A.Proof.default
         | _ -> ())

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

  module Debug_ = struct
    let pp out _ = Fmt.string out "cc"
  end

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

  (* TODO:
      CC.set_as_lit cc n (Lit.abs lit);
     *)

  (* assert that this boolean literal holds.
     if a lit is [= a b], merge [a] and [b];
     otherwise merge the atom with true/false *)
  let assert_lit cc lit : unit =
    let t = Lit.term lit in
    Log.debugf 5 (fun k->k "(@[cc.assert_lit@ %a@])" Lit.pp lit);
    let sign = Lit.sign lit in
    begin match CC_A.cc_view t with
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
        (* TODO: use oriented merge (force direction [n -> rhs]) *)
        merge_classes cc n rhs (Expl.mk_lit lit)
    end

  let[@inline] assert_lits cc lits : unit =
    Iter.iter (assert_lit cc) lits

  (* raise a conflict *)
  let raise_conflict_from_expl cc (acts:actions) expl =
    Log.debugf 5
      (fun k->k "(@[cc.theory.raise-conflict@ :expl %a@])" Expl.pp expl);
    let lits = explain_decompose cc [] expl in
    let lits = List.rev_map Lit.neg lits in
    raise_conflict cc acts lits

  let merge cc n1 n2 expl =
    Log.debugf 5
      (fun k->k "(@[cc.theory.merge@ :n1 %a@ :n2 %a@ :expl %a@])" N.pp n1 N.pp n2 Expl.pp expl);
    merge_classes cc n1 n2 expl

  let on_merge cc f = cc.on_merge <- f :: cc.on_merge
  let on_new_term cc f = cc.on_new_term <- f :: cc.on_new_term
  let on_conflict cc f = cc.on_conflict <- f :: cc.on_conflict
  let on_propagate cc f = cc.on_propagate <- f :: cc.on_propagate

  let create ?(stat=Stat.global)
      ?(on_merge=[]) ?(on_new_term=[]) ?(on_conflict=[]) ?(on_propagate=[])
      ?(size=`Big)
      (tst:term_state) : t =
    let size = match size with `Small -> 128 | `Big -> 2048 in
    let rec cc = {
      tst;
      tbl = T_tbl.create size;
      signatures_tbl = Sig_tbl.create size;
      on_merge;
      on_new_term;
      on_conflict;
      on_propagate;
      pending=Vec.create();
      combine=Vec.create();
      undo=Backtrack_stack.create();
      true_;
      false_;
      stat;
      count_conflict=Stat.mk_int stat "cc.conflicts";
      count_props=Stat.mk_int stat "cc.propagations";
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

  (* model: return all the classes *)
  let get_model (cc:t) : repr Iter.t Iter.t =
    all_classes cc |> Iter.map N.iter_class
end
