open Sidekick_core
module View = Sidekick_core.CC_view

type ('f, 't, 'ts) view = ('f, 't, 'ts) View.t =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 't
  | If of 't * 't * 't
  | Eq of 't * 't
  | Not of 't
  | Opaque of 't (* do not enter *)

module type S = Sidekick_core.CC_S

module Make (A: CC_ARG)
  : S with module T = A.T
       and module Lit = A.Lit
       and type proof = A.proof
       and module Actions = A.Actions
= struct
  module T = A.T
  module Lit = A.Lit
  module Actions = A.Actions
  module P = Actions.P
  type term = T.Term.t
  type term_store = T.Term.store
  type lit = Lit.t
  type fun_ = T.Fun.t
  type proof = A.proof
  type dproof = proof -> unit
  type actions = Actions.t

  module Term = T.Term
  module Fun = T.Fun

  (* nodes are represented as integer offsets *)
  module Node0 : sig
    include Int_id.S
    module NVec : Vec_sig.S with type elt := t
    module Set : CCSet.S with type elt = t
    module Tbl : CCHashtbl.S with type key = t
  end = struct
    include Int_id.Make()
    module NVec = VecI32
    module Set = Util.Int_set
    module Tbl = Util.Int_tbl
  end
  module NVec = Node0.NVec

  type node = Node0.t
  type repr = node (* a node that is representative of its class *)

  (* we keep several bitvectors in the congruence closure,
     each mapping nodes to a boolean.
     An individual bitvector is represented as its offset in the list of
     bitvectors. *)
  module Bit_field : Int_id.S = Int_id.Make()
  type bitfield = Bit_field.t

  (* TODO: sparse vec for n_sig0? *)
  (* the node store, holds data for all the nodes *)
  type node_store = {
    n_term: term Vec.t; (* term for the node *)
    n_sig0: signature Vec.t; (* initial signature, if any. to be modified. *)
    n_parents: node Bag.t Vec.t; (* node -> parents(class(node)) *)
    n_root: NVec.t; (* node -> repr(class(node)) *)
    n_next: NVec.t; (* node -> next(class(node)) *)
    n_size: VecI32.t; (* node -> size(class(node)) *)
    n_as_lit: lit Node0.Tbl.t; (* root -> literal, if any *)
    n_expl: explanation_forest_link Vec.t; (* proof forest *)
    n_bitfields: Bitvec.t Vec.t; (* bitfield idx -> atom -> bool *)
  }

  (* TODO: use node array for 3rd param *)
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
    | E_theory of explanation

  module N = struct
    include Node0
    type store = node_store

    let[@inline] term self n = Vec.get self.n_term (n:t:>int)
    let[@inline] pp self out n = Term.pp out (term self n)

    let[@inline] sig0 self n = Vec.get self.n_sig0 (n:t:>int)
    let[@inline] set_sig0 self n s = Vec.set self.n_sig0 (n:t:>int) s
    let[@inline] size self n = VecI32.get self.n_size (n:t:>int)
    let[@inline] set_size self n sz = VecI32.set self.n_size (n:t:>int) sz
    let[@inline] next self n = NVec.get self.n_next (n:t:>int)
    let[@inline] set_next self n r = NVec.set self.n_next (n:t:>int) r
    let[@inline] root self n = NVec.get self.n_root (n:t:>int)
    let[@inline] set_root self n r = NVec.set self.n_root (n:t:>int) r
    let[@inline] expl self n = Vec.get self.n_expl (n:t:>int)
    let[@inline] set_expl self n e = Vec.set self.n_expl (n:t:>int) e
    let[@inline] parents self n = Vec.get self.n_parents (n:t:>int)
    let[@inline] set_parents self n b = Vec.set self.n_parents (n:t:>int) b
    let[@inline] upd_parents ~f self n = set_parents self n (f (parents self n))

    let[@inline] as_lit self n = Tbl.get self.n_as_lit n
    let[@inline] set_as_lit self n lit = Tbl.replace self.n_as_lit n lit
    let[@inline] clear_as_lit self n = Tbl.remove self.n_as_lit n

    let alloc (self:store) (t:term) : t =
      let {
        n_term; n_sig0; n_parents; n_root; n_next; n_size
      } = self in
      let n = Node0.of_int_unsafe (Vec.size n_term) in
      Vec.push n_term t;
      Vec.push n_sig0 (Opaque n); (* will be updated *)
      Vec.push n_parents Bag.empty;
      NVec.push n_root n;
      NVec.push n_next n;
      VecI32.push n_size 1;
      n

    (* dealloc node. It must be the last node allocated. *)
    let dealloc (self:store) (n:t) : unit =
      assert ((n:>int) + 1 = Vec.size self.n_term);
      let {
        n_term; n_sig0; n_parents; n_root; n_next; n_size
      } = self in
      ignore (Vec.pop_exn n_term : term);
      ignore (Vec.pop_exn n_sig0 : signature);
      ignore (Vec.pop_exn n_parents : _ Bag.t);
      ignore (NVec.pop n_root : t);
      ignore (NVec.pop n_next : t);
      ignore (VecI32.pop n_size : int);
      ()

    let[@inline] is_root (self:store) (n:node) : bool =
      let n2 = NVec.get self.n_root (n:t:>int) in
      equal n n2

    (* traverse the equivalence class of [n] *)
    let iter_class_ (self:store) (n:t) : t Iter.t =
      fun yield ->
        let rec aux u =
          yield u;
          let u2 = NVec.get self.n_next (u:t:>int) in
          if not (equal n u2) then aux u2
        in
        aux n

    let[@inline] iter_class self n =
      assert (is_root self n);
      iter_class_ self n

    let[@inline] iter_parents self (n:node) : node Iter.t =
      assert (is_root self n);
      Bag.to_iter (Vec.get self.n_parents (n:t:>int))

    type nonrec bitfield = bitfield

    let alloc_bitfield ~descr (self:store) : bitfield =
      Log.debugf 5 (fun k->k "(@[cc.allocate-bit-field@ :descr %s@])" descr);
      let field = Bit_field.of_int_unsafe (Vec.size self.n_bitfields) in
      Vec.push self.n_bitfields (Bitvec.create());
      field

    let create () : store = {
      n_term=Vec.create ();
      n_sig0=Vec.create ();
      n_root=NVec.create ~cap:1024 ();
      n_next=NVec.create ~cap:1024 ();
      n_parents=Vec.create ();
      n_size=VecI32.create ~cap:1024 ();
      n_expl=Vec.create ();
      n_as_lit=Tbl.create 256;
      n_bitfields=Vec.create();
    }

    let[@inline] get_field (self:store) (f:bitfield) (n:t) =
      let bv = Vec.get self.n_bitfields (f:>int) in
      Bitvec.get bv (n:t:>int)

    let[@inline] set_field (self:store) (f:bitfield) (n:t) b : unit =
      let bv = Vec.get self.n_bitfields (f:>int) in
      Bitvec.set bv (n:t:>int) b

    (* non-recursive, inlinable function for [find] *)
    let[@inline] find (self:store) (n:t) : repr =
      let n2 = NVec.get self.n_root (n:t:>int) in
      assert (is_root self n2);
      n2

    let[@inline] same_class self (n1:node) (n2:node): bool =
      equal (find self n1) (find self n2)
  end

  module N_tbl = Node0.Tbl

  module Expl = struct
    type t = explanation

    let rec pp nstore out (e:explanation) : unit =
      let ppn = N.pp nstore in
      let pp = pp nstore in
      match e with
      | E_reduction -> Fmt.string out "reduction"
      | E_lit lit -> Lit.pp out lit
      | E_congruence (n1,n2) -> Fmt.fprintf out "(@[congruence@ %a@ %a@])" ppn n1 ppn n2
      | E_merge (a,b) ->
        Fmt.fprintf out "(@[merge@ %a@ %a@])" ppn a ppn b
      | E_merge_t (a,b) ->
        Fmt.fprintf out "(@[<hv>merge@ @[:n1 %a@]@ @[:n2 %a@]@])" Term.pp a Term.pp b
      | E_theory e -> Fmt.fprintf out "(@[th@ %a@])" pp e
      | E_and (a,b) ->
        Format.fprintf out "(@[<hv1>and@ %a@ %a@])" pp a pp b

    let mk_reduction : t = E_reduction
    let[@inline] mk_congruence n1 n2 : t = E_congruence (n1,n2)
    let[@inline] mk_merge a b : t = if N.equal a b then mk_reduction else E_merge (a,b)
    let[@inline] mk_merge_t a b : t = if Term.equal a b then mk_reduction else E_merge_t (a,b)
    let[@inline] mk_lit l : t = E_lit l
    let mk_theory e = E_theory e

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
      | App_ho (f1,a1), App_ho (f2,a2) ->
        N.equal f1 f2 && N.equal a1 a2
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
      | App_ho (f, a) -> H.combine3 30 (N.hash f) (N.hash a)
      | Eq (a,b) -> H.combine3 40 (N.hash a) (N.hash b)
      | Opaque u -> H.combine2 50 (N.hash u)
      | If (a,b,c) -> H.combine4 60 (N.hash a)(N.hash b)(N.hash c)
      | Not u -> H.combine2 70 (N.hash u)

    let pp nstore out s =
      let ppn = N.pp nstore in
      match s with
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list ppn) l
      | App_ho (f, a) -> Fmt.fprintf out "(@[%a@ %a@])" ppn f ppn a
      | Opaque t -> ppn out t
      | Not u -> Fmt.fprintf out "(@[not@ %a@])" ppn u
      | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" ppn a ppn b
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" ppn a ppn b ppn c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)
  module T_tbl = CCHashtbl.Make(Term)

  type combine_task =
    | CT_merge of node * node * explanation

  type t = {
    tst: term_store;
    nstore: N.store;
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
    mutable on_pre_merge: ev_on_pre_merge list;
    mutable on_post_merge: ev_on_post_merge list;
    mutable on_new_term: ev_on_new_term list;
    mutable on_conflict: ev_on_conflict list;
    mutable on_propagate: ev_on_propagate list;
    mutable on_is_subterm : ev_on_is_subterm list;
    mutable new_merges: bool;
    field_marked_explain: N.bitfield; (* used to mark traversed nodes when looking for a common ancestor *)
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
     See "fast congruence closure and extensions", Nieuwenhuis&al, page 14 *)

  and ev_on_pre_merge = t -> actions -> N.t -> N.t -> Expl.t -> unit
  and ev_on_post_merge = t -> actions -> N.t -> N.t -> unit
  and ev_on_new_term = t -> N.t -> term -> unit
  and ev_on_conflict = t -> th:bool -> lit list -> unit
  and ev_on_propagate = t -> lit -> (unit -> lit list * (proof -> unit)) -> unit
  and ev_on_is_subterm = N.t -> term -> unit

  let[@inline] n_true cc = Lazy.force cc.true_
  let[@inline] n_false cc = Lazy.force cc.false_
  let n_bool cc b = if b then n_true cc else n_false cc
  let[@inline] term_store (cc:t) = cc.tst
  let[@inline] n_store (cc:t) = cc.nstore

  (* new bitfield *)
  let allocate_bitfield ~descr self = N.alloc_bitfield ~descr self.nstore

  (* iterate on existing bitfields *)
  let[@inline] iter_bitfields (self:t) ~(f:Bit_field.t -> unit) : unit =
    for i=0 to Vec.size self.nstore.n_bitfields - 1 do
      f (Bit_field.of_int_unsafe i)
    done

  let[@inline] on_backtrack cc f : unit =
    Backtrack_stack.push_if_nonzero_level cc.undo f

  let[@inline] get_bitfield cc field n =
    N.get_field cc.nstore field n

  let set_bitfield cc field b n =
    let old = N.get_field cc.nstore field n in
    if old <> b then (
      on_backtrack cc (fun () -> N.set_field cc.nstore field n old);
      N.set_field cc.nstore field n b;
    )

  (* check if [t] is in the congruence closure.
     Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
  let[@inline] mem (cc:t) (t:term): bool = T_tbl.mem cc.tbl t

  (* print full state *)
  let pp_full out (cc:t) : unit =
    let nstore = cc.nstore in
    let ppn = N.pp nstore in
    let pp_next out n =
      Fmt.fprintf out "@ :next %a" ppn (N.next nstore n) in
    let pp_root out n =
      if N.is_root nstore n
      then Fmt.string out " :is-root"
      else Fmt.fprintf out "@ :root %a" ppn (N.root nstore n) in
    let pp_expl out n = match N.expl nstore n with
      | FL_none -> ()
      | FL_some e ->
        Fmt.fprintf out " (@[:forest %a :expl %a@])"
          ppn e.next (Expl.pp nstore) e.expl
    in
    let pp_n out n =
      Fmt.fprintf out "(@[%a%a%a%a@])"
        Term.pp (N.term nstore n) pp_root n pp_next n pp_expl n
    and pp_sig_e out (s,n) =
      Fmt.fprintf out "(@[<1>%a@ ~~> %a%a@])" (Signature.pp nstore) s ppn n pp_root n
    in
    Fmt.fprintf out
      "(@[@{<yellow>cc.state@}@ (@[<hv>:nodes@ %a@])@ (@[<hv>:sig-tbl@ %a@])@])"
      (Util.pp_iter ~sep:" " pp_n) (T_tbl.values cc.tbl)
      (Util.pp_iter ~sep:" " pp_sig_e) (Sig_tbl.to_iter cc.signatures_tbl)

  (* compute up-to-date signature *)
  let update_sig (self:t) (s:signature) : Signature.t =
    let find = N.find self.nstore in
    View.map_view s
      ~f_f:(fun x->x)
      ~f_t:find
      ~f_ts:(List.map find)

  (* find whether the given (parent) term corresponds to some signature
     in [signatures_] *)
  let[@inline] find_signature cc (s:signature) : repr option =
    Sig_tbl.get cc.signatures_tbl s

  (* add to signature table. Assume it's not present already *)
  let add_signature cc (s:signature) (n:node) : unit =
    assert (not @@ Sig_tbl.mem cc.signatures_tbl s);
    let nstore = cc.nstore in
    Log.debugf 50
      (fun k->k "(@[cc.add-sig@ %a@ ~~> %a@])" (Signature.pp nstore) s (N.pp nstore) n);
    on_backtrack cc (fun () -> Sig_tbl.remove cc.signatures_tbl s);
    Sig_tbl.add cc.signatures_tbl s n

  let push_pending cc t : unit =
    let nstore = cc.nstore in
    Log.debugf 50 (fun k->k "(@[<hv1>cc.push-pending@ %a@])" (N.pp nstore) t);
    Vec.push cc.pending t

  let merge_classes cc t u e : unit =
    if t != u && not (N.same_class cc.nstore t u) then (
      Log.debugf 50
        (fun k->let nstore=cc.nstore in
          k "(@[<hv1>cc.push-combine@ %a ~@ %a@ :expl %a@])"
            (N.pp nstore) t (N.pp nstore) u (Expl.pp nstore) e);
      Vec.push cc.combine @@ CT_merge (t,u,e)
    )

  (* re-root the explanation tree of the equivalence class of [n]
     so that it points to [n].
     postcondition: [n.n_expl = None] *)
  let[@unroll 2] rec reroot_expl (cc:t) (n:node): unit =
    begin match N.expl cc.nstore n with
      | FL_none -> () (* already root *)
      | FL_some {next=u; expl=e_n_u} ->
        (* reroot to [u], then invert link between [u] and [n] *)
        reroot_expl cc u;
        N.set_expl cc.nstore u (FL_some {next=n; expl=e_n_u});
        N.set_expl cc.nstore n FL_none;
    end

  let raise_conflict_ (cc:t) ~th (acts:actions) (e:lit list) p : _ =
    Profile.instant "cc.conflict";
    (* clear tasks queue *)
    Vec.clear cc.pending;
    Vec.clear cc.combine;
    List.iter (fun f -> f cc ~th e) cc.on_conflict;
    Stat.incr cc.count_conflict;
    Actions.raise_conflict acts e p

  let[@inline] all_classes cc : repr Iter.t =
    T_tbl.values cc.tbl
    |> Iter.filter (N.is_root cc.nstore)

  (* find the closest common ancestor of [a] and [b] in the proof forest.

     Precond:
     - [a] and [b] are in the same class
     - no node has the flag [field_marked_explain] on
     Invariants:
     - if [n] is marked, then all the predecessors of [n]
       from [a] or [b] are marked too.
  *)
  let find_common_ancestor cc (a:node) (b:node) : node =
    (* catch up to the other node *)
    let rec find1 a =
      if N.get_field cc.nstore cc.field_marked_explain a then a
      else (
        match N.expl cc.nstore a with
        | FL_none -> assert false
        | FL_some r -> find1 r.next
      )
    in
    let rec find2 a b =
      if N.equal a b then a
      else if N.get_field cc.nstore cc.field_marked_explain a then a
      else if N.get_field cc.nstore cc.field_marked_explain b then b
      else (
        N.set_field cc.nstore cc.field_marked_explain a true;
        N.set_field cc.nstore cc.field_marked_explain b true;
        match N.expl cc.nstore a, N.expl cc.nstore b with
        | FL_some r1, FL_some r2 -> find2 r1.next r2.next
        | FL_some r, FL_none -> find1 r.next
        | FL_none, FL_some r -> find1 r.next
        | FL_none, FL_none -> assert false (* no common ancestor *)
      )

    in
    (* cleanup tags on nodes traversed in [find2] *)
    let rec cleanup_ n =
      if N.get_field cc.nstore cc.field_marked_explain n then (
        N.set_field cc.nstore cc.field_marked_explain n false;
        match N.expl cc.nstore n with
        | FL_none -> ()
        | FL_some {next;_} -> cleanup_ next;
      )
    in
    let n = find2 a b in
    cleanup_ a;
    cleanup_ b;
    n

  (* decompose explanation [e] into a list of literals added to [acc] *)
  let rec explain_decompose_expl cc ~th (acc:lit list) (e:explanation) : _ list =
    Log.debugf 5 (fun k->k "(@[cc.decompose_expl@ %a@])" (Expl.pp cc.nstore) e);
    match e with
    | E_reduction -> acc
    | E_congruence (n1, n2) ->
      begin match N.sig0 cc.nstore n1, N.sig0 cc.nstore n2 with
        | App_fun (f1, a1), App_fun (f2, a2) ->
          assert (Fun.equal f1 f2);
          assert (List.length a1 = List.length a2);
          List.fold_left2 (explain_equal cc ~th) acc a1 a2
        | App_ho (f1, a1), App_ho (f2, a2) ->
          let acc = explain_equal cc ~th acc f1 f2 in
          explain_equal cc ~th acc a1 a2
        | If (a1,b1,c1), If (a2,b2,c2) ->
          let acc = explain_equal cc ~th acc a1 a2 in
          let acc = explain_equal cc ~th acc b1 b2 in
          explain_equal cc ~th acc c1 c2
        | _ ->
          assert false
      end
    | E_lit lit -> lit :: acc
    | E_theory e' ->
      th := true; explain_decompose_expl cc ~th acc e'
    | E_merge (a,b) -> explain_equal cc ~th acc a b
    | E_merge_t (a,b) ->
      (* find nodes for [a] and [b] on the fly *)
      begin match T_tbl.find cc.tbl a, T_tbl.find cc.tbl b with
        | a, b -> explain_equal cc ~th acc a b
        | exception Not_found ->
          Error.errorf "expl: cannot find node(s) for %a, %a" Term.pp a Term.pp b
      end
    | E_and (a,b) ->
      let acc = explain_decompose_expl cc ~th acc a in
      explain_decompose_expl cc ~th acc b

  and explain_equal (cc:t) ~th (acc:lit list) (a:node) (b:node) : _ list =
    let nstore = cc.nstore in
    Log.debugf 5
      (fun k->k "(@[cc.explain_loop.at@ %a@ =?= %a@])"
          (N.pp nstore) a (N.pp nstore) b);
    assert (N.same_class nstore a b);
    let ancestor = find_common_ancestor cc a b in
    let acc = explain_along_path cc ~th acc a ancestor in
    explain_along_path cc ~th acc b ancestor

  (* explain why [a = parent_a], where [a -> ... -> target] in the
     proof forest *)
  and explain_along_path cc ~th acc (a:node) (target:node) : _ list =
    let rec aux acc n =
      if n == target then acc
      else (
        match N.expl cc.nstore n with
        | FL_none -> assert false
        | FL_some {next=next_n; expl=expl} ->
          let acc = explain_decompose_expl cc ~th acc expl in
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
    Log.debugf 15 (fun k->k "(@[cc.add-term@ %a@])" Term.pp t);

    let n = N.alloc cc.nstore t in

    (* register sub-terms, add [t] to their parent list, and return the
       corresponding initial signature *)
    let sig0 = compute_sig0 cc n in

    (* remove term when we backtrack *)
    on_backtrack cc
      (fun () ->
         Log.debugf 15 (fun k->k "(@[cc.remove-term@ %a@])" Term.pp t);
         N.dealloc cc.nstore n;
         T_tbl.remove cc.tbl t);

    (* add term to the table *)
    T_tbl.add cc.tbl t n;

    begin match sig0 with
      | Opaque _ | Bool _ -> ()
      | App_ho _ | App_fun _ | If _ | Eq _ | Not _ ->
        (* [n] might be merged with other equiv classes *)
        push_pending cc n;
    end;

    List.iter (fun f -> f cc n t) cc.on_new_term;
    n

  (* compute the initial signature of the given node *)
  and compute_sig0 (self:t) (n:node) : Signature.t =
    (* add sub-term to [cc], and register [n] to its parents.
       Note that we return the exact sub-term, to get proper
       explanations, but we add to the sub-term's root's parent list. *)
    let deref_sub (u:term) : node =
      let sub = add_term_rec_ self u in
      (* add [n] to [sub.root]'s parent list *)
      begin
        let sub_r = N.find self.nstore sub in
        let old_parents = N.parents self.nstore sub_r in
        if Bag.is_empty old_parents then (
          (* first time it has parents: tell watchers that this is a subterm *)
          List.iter (fun f -> f sub u) self.on_is_subterm;
        );
        on_backtrack self (fun () -> N.set_parents self.nstore sub_r old_parents);
        N.upd_parents self.nstore sub_r ~f:(fun p -> Bag.cons n p);
      end;
      sub
    in
    begin match A.cc_view (N.term self.nstore n) with
      | Bool _ | Opaque _ -> Opaque n
      | Eq (a,b) ->
        let a = deref_sub a in
        let b = deref_sub b in
        Eq (a,b)
      | Not u -> Not (deref_sub u)
      | App_fun (f, args) ->
        let args = args |> Iter.map deref_sub |> Iter.to_list in
        if args<>[] then (
          App_fun (f, args)
        ) else Opaque n
      | App_ho (f, a ) ->
        let f = deref_sub f in
        let a = deref_sub a in
        App_ho (f, a)
      | If (a,b,c) ->
        If (deref_sub a, deref_sub b, deref_sub c)
    end

  let[@inline] add_term cc t : node = add_term_rec_ cc t

  let mem_term = mem

  let set_as_lit self (n:node) (lit:lit) : unit =
    match N.as_lit self.nstore n with
    | Some _ -> ()
    | None ->
      Log.debugf 15 (fun k->k "(@[cc.set-as-lit@ %a@ %a@])"
                        (N.pp self.nstore) n Lit.pp lit);
      on_backtrack self (fun () -> N.clear_as_lit self.nstore n);
      N.set_as_lit self.nstore n lit

  (* is [n] true or false? *)
  let n_is_bool_value (self:t) n : bool =
    N.equal n (n_true self) || N.equal n (n_false self)

  (* main CC algo: add terms from [pending] to the signature table,
     check for collisions *)
  let rec update_tasks (self:t) (acts:actions) : unit =
    while not (Vec.is_empty self.pending && Vec.is_empty self.combine) do
      while not @@ Vec.is_empty self.pending do
        task_pending_ self (Vec.pop_exn self.pending);
      done;
      while not @@ Vec.is_empty self.combine do
        task_combine_ self acts (Vec.pop_exn self.combine);
      done;
    done

  and task_pending_ (self:t) (n:node) : unit =
    (* check if some parent collided *)
    begin match N.sig0 self.nstore n with
      | Opaque _ -> () (* no-op *)
      | Eq (a,b) ->
        (* if [a=b] is now true, merge [(a=b)] and [true] *)
        if N.same_class self.nstore a b then (
          let expl = Expl.mk_merge a b in
          Log.debugf 5
            (fun k->k "(@[pending.eq@ %a@ :r1 %a@ :r2 %a@])"
                (N.pp self.nstore) n (N.pp self.nstore) a
                (N.pp self.nstore) b);
          merge_classes self n (n_true self) expl
        )
      | Not u ->
        (* [u = bool ==> not u = not bool] *)
        let r_u = N.find self.nstore u in
        if N.equal r_u (n_true self) then (
          let expl = Expl.mk_merge u (n_true self) in
          merge_classes self n (n_false self) expl
        ) else if N.equal r_u (n_false self) then (
          let expl = Expl.mk_merge u (n_false self) in
          merge_classes self n (n_true self) expl
        )
      | s0 ->
        (* update the signature by using [find] on each sub-node *)
        let s = update_sig self s0 in
        begin match find_signature self s with
          | None ->
            (* add to the signature table [sig(n) --> n] *)
            add_signature self s n
          | Some u when N.equal n u -> ()
          | Some u ->
            (* [t1] and [t2] must be applications of the same symbol to
                 arguments that are pairwise equal *)
            assert (n != u);
            let expl = Expl.mk_congruence n u in
            merge_classes self n u expl
        end
    end

  and[@inline] task_combine_ cc acts = function
    | CT_merge (a,b,e_ab) ->
      cc.new_merges <- true;
      task_merge_ cc acts a b e_ab

  (* main CC algo: merge equivalence classes in [st.combine].
     @raise Exn_unsat if merge fails *)
  and task_merge_ self acts a b e_ab : unit =
    let nstore = self.nstore in
    let ra = N.find nstore a in
    let rb = N.find nstore b in
    if not @@ N.equal ra rb then (
      assert (N.is_root nstore ra);
      assert (N.is_root nstore rb);
      Stat.incr self.count_merge;
      (* check we're not merging [true] and [false] *)
      if (N.equal ra (n_true self) && N.equal rb (n_false self)) ||
         (N.equal rb (n_true self) && N.equal ra (n_false self)) then (
        Log.debugf 5
          (fun k->
             let ppn = N.pp nstore in
             k "(@[<hv>cc.merge.true_false_conflict@ \
                     @[:r1 %a@ :t1 %a@]@ @[:r2 %a@ :t2 %a@]@ :e_ab %a@])"
            ppn ra ppn a ppn rb ppn b (Expl.pp nstore) e_ab);
        let th = ref false in
        (* TODO:
           C1: P.true_neq_false
           C2: lemma [lits |- true=false]  (and resolve on theory proofs)
           C3: r1 C1 C2
        *)
        let lits = explain_decompose_expl self ~th [] e_ab in
        let lits = explain_equal self ~th lits a ra in
        let lits = explain_equal self ~th lits b rb in
        let emit_proof p =
          let p_lits = Iter.of_list lits |> Iter.map Lit.neg in
          P.lemma_cc p_lits p in
        raise_conflict_ self ~th:!th acts (List.rev_map Lit.neg lits) emit_proof
      );
      (* We will merge [r_from] into [r_into].
         we try to ensure that [size ra <= size rb] in general, but always
         keep values as representative *)
      let r_from, r_into =
        if n_is_bool_value self ra then rb, ra
        else if n_is_bool_value self rb then ra, rb
        else if N.size nstore ra > N.size nstore rb then rb, ra
        else ra, rb
      in
      (* when merging terms with [true] or [false], possibly propagate them to SAT *)
      let merge_bool r1 t1 r2 t2 =
        if N.equal r1 (n_true self) then (
          propagate_bools self acts r2 t2 r1 t1 e_ab true
        ) else if N.equal r1 (n_false self) then (
          propagate_bools self acts r2 t2 r1 t1 e_ab false
        )
      in
      merge_bool ra a rb b;
      merge_bool rb b ra a;
      (* perform [union r_from r_into] *)
      Log.debugf 15 (fun k->k "(@[cc.merge@ :from %a@ :into %a@])"
                        (N.pp nstore) r_from (N.pp nstore) r_into);
      (* call [on_pre_merge] functions, and merge theory data items *)
      begin
        (* explanation is [a=ra & e_ab & b=rb] *)
        let expl = Expl.mk_list [e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb] in
        List.iter (fun f -> f self acts r_into r_from expl) self.on_pre_merge;
      end;
      begin
        (* parents might have a different signature, check for collisions *)
        N.iter_parents nstore r_from
          (fun parent -> push_pending self parent);
        (* for each node in [r_from]'s class, make it point to [r_into] *)
        N.iter_class nstore r_from
          (fun u ->
             assert (N.root nstore u == r_from);
             N.set_root nstore u r_into);
        (* capture current state *)
        let r_into_old_next = N.next nstore r_into in
        let r_from_old_next = N.next nstore r_from in
        let r_into_old_parents = N.parents nstore r_into in
        (* swap [into.next] and [from.next], merging the classes *)
        N.set_next nstore r_into r_from_old_next;
        N.set_next nstore r_from r_into_old_next;
        N.upd_parents nstore r_into ~f:(fun p -> Bag.append p (N.parents nstore r_from));
        N.set_size nstore r_into (N.size nstore r_into + N.size nstore r_from);

        (* merge bitfields, and backtrack changes *)

        iter_bitfields self ~f:(fun field ->
            let b_into = N.get_field nstore field r_into in
            if not b_into then (
              let b_from = N.get_field nstore field r_from in
              if b_from then (
                (* we modify the field of [r_into], remember to undo that *)
                on_backtrack self (fun () -> N.set_field nstore field r_into false);
                N.set_field nstore field r_into true;
              );
            ));

        (* on backtrack, unmerge classes and restore the pointers to [r_from] *)
        on_backtrack self
          (fun () ->
             Log.debugf 15
               (fun k->k "(@[cc.undo_merge@ :from %a :into %a@])"
                   (N.pp nstore) r_from (N.pp nstore) r_into);
             N.set_next nstore r_into r_into_old_next;
             N.set_next nstore r_from r_from_old_next;
             N.set_parents nstore r_into r_into_old_parents;
             (* NOTE: this must come after the restoration of [next] pointers,
                otherwise we'd iterate on too big a class *)
             N.iter_class nstore r_from (fun u -> N.set_root nstore u r_from);
             N.set_size nstore r_into (N.size nstore r_into - N.size nstore r_from);
          );
      end;
      (* update explanations (a -> b), arbitrarily.
         Note that here we merge the classes by adding a bridge between [a]
         and [b], not their roots. *)
      begin
        reroot_expl self a;
        assert (N.expl nstore a == FL_none);
        (* on backtracking, link may be inverted, but we delete the one
           that bridges between [a] and [b] *)
        on_backtrack self
          (fun () -> match N.expl nstore a, N.expl nstore b with
             | FL_some e, _ when N.equal e.next b -> N.set_expl nstore a FL_none
             | _, FL_some e when N.equal e.next a -> N.set_expl nstore b FL_none
             | _ -> assert false);
        N.set_expl nstore a (FL_some {next=b; expl=e_ab});
      end;
      (* call [on_post_merge] *)
      begin
        List.iter (fun f -> f self acts r_into r_from) self.on_post_merge;
      end;
    )

  (* we are merging [r1] with [r2==Bool(sign)], so propagate each term [u1]
     in the equiv class of [r1] that is a known literal back to the SAT solver
     and which is not the one initially merged.
     We can explain the propagation with [u1 = t1 =e= t2 = r2==bool] *)
  and propagate_bools (self:t) acts r1 t1 r2 t2 (e_12:explanation) sign : unit =
    (* explanation for [t1 =e= t2 = r2] *)
    let half_expl = lazy (
      let th = ref false in
      let lits = explain_decompose_expl self ~th [] e_12 in
      th, explain_equal self ~th lits r2 t2
    ) in
    (* TODO: flag per class, `or`-ed on merge, to indicate if the class
       contains at least one lit *)
    N.iter_class self.nstore r1
      (fun u1 ->
         (* propagate if:
            - [u1] is a proper literal
            - [t2 != r2], because that can only happen
              after an explicit merge (no way to obtain that by propagation)
         *)
         match N.as_lit self.nstore u1 with
         | Some lit when not (N.equal r2 t2) ->
           let lit = if sign then lit else Lit.neg lit in (* apply sign *)
           Log.debugf 5 (fun k->k "(@[cc.bool_propagate@ %a@])" Lit.pp lit);
           (* complete explanation with the [u1=t1] chunk *)
           let reason =
             let e = lazy (
               let lazy (th, acc) = half_expl in
               let lits = explain_equal self ~th acc u1 t1 in
               let emit_proof p =
                 (* make a tautology, not a true guard *)
                 let p_lits = Iter.cons lit (Iter.of_list lits |> Iter.map Lit.neg) in
                 P.lemma_cc p_lits p
               in
               lits, emit_proof
             ) in
             fun () -> Lazy.force e
           in
           List.iter (fun f -> f self lit reason) self.on_propagate;
           Stat.incr self.count_props;
           Actions.propagate acts lit ~reason
         | _ -> ())

  module Debug_ = struct
    let pp out _ = Fmt.string out "cc"
  end

  let add_seq cc seq =
    seq (fun t -> ignore @@ add_term_rec_ cc t);
    ()

  let[@inline] push_level (self:t) : unit =
    Backtrack_stack.push_level self.undo

  let pop_levels (self:t) n : unit =
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
    Log.debugf 15 (fun k->k "(@[cc.assert-lit@ %a@])" Lit.pp lit);
    let sign = Lit.sign lit in
    begin match A.cc_view t with
      | Eq (a,b) when sign ->
        let a = add_term cc a in
        let b = add_term cc b in
        (* merge [a] and [b] *)
        merge_classes cc a b (Expl.mk_lit lit)
      | _ ->
        (* equate t and true/false *)
        let rhs = if sign then n_true cc else n_false cc in
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
  let raise_conflict_from_expl self (acts:actions) expl =
    Log.debugf 5
      (fun k->k "(@[cc.theory.raise-conflict@ :expl %a@])" (Expl.pp self.nstore) expl);
    let th = ref true in
    let lits = explain_decompose_expl self ~th [] expl in
    let lits = List.rev_map Lit.neg lits in
    let emit_proof p =
      let p_lits = Iter.of_list lits in
      P.lemma_cc p_lits p
    in
    raise_conflict_ self ~th:!th acts lits emit_proof

  let merge (self:t) n1 n2 expl =
    Log.debugf 5
      (fun k->k "(@[cc.theory.merge@ :n1 %a@ :n2 %a@ :expl %a@])"
          (N.pp self.nstore) n1 (N.pp self.nstore) n2 (Expl.pp self.nstore) expl);
    assert (T.Ty.equal (T.Term.ty (N.term self.nstore n1)) (T.Term.ty (N.term self.nstore n2)));
    merge_classes self n1 n2 expl

  let[@inline] merge_t cc t1 t2 expl =
    merge cc (add_term cc t1) (add_term cc t2) expl

  let explain_eq cc n1 n2 : lit list =
    let th = ref true in
    explain_equal cc ~th [] n1 n2

  let on_pre_merge cc f = cc.on_pre_merge <- f :: cc.on_pre_merge
  let on_post_merge cc f = cc.on_post_merge <- f :: cc.on_post_merge
  let on_new_term cc f = cc.on_new_term <- f :: cc.on_new_term
  let on_conflict cc f = cc.on_conflict <- f :: cc.on_conflict
  let on_propagate cc f = cc.on_propagate <- f :: cc.on_propagate
  let on_is_subterm cc f = cc.on_is_subterm <- f :: cc.on_is_subterm

  let create ?(stat=Stat.global)
      ?(on_pre_merge=[]) ?(on_post_merge=[]) ?(on_new_term=[])
      ?(on_conflict=[]) ?(on_propagate=[]) ?(on_is_subterm=[])
      ?(size=`Big)
      (tst:term_store) : t =
    let size = match size with `Small -> 128 | `Big -> 2048 in
    let nstore = N.create() in
    let field_marked_explain = N.alloc_bitfield ~descr:"mark-explain" nstore in
    assert ((field_marked_explain :> int) = 0);
    let rec cc = {
      tst;
      nstore;
      tbl = T_tbl.create size;
      signatures_tbl = Sig_tbl.create size;
      on_pre_merge;
      on_post_merge;
      on_new_term;
      on_conflict;
      on_propagate;
      on_is_subterm;
      pending=Vec.create();
      combine=Vec.create();
      undo=Backtrack_stack.create();
      true_;
      false_;
      stat;
      new_merges=false;
      field_marked_explain;
      count_conflict=Stat.mk_int stat "cc.conflicts";
      count_props=Stat.mk_int stat "cc.propagations";
      count_merge=Stat.mk_int stat "cc.merges";
    } and true_ = lazy (
        add_term cc (Term.bool tst true)
      ) and false_ = lazy (
        add_term cc (Term.bool tst false)
      )
    in
    ignore (Lazy.force true_ : node);
    ignore (Lazy.force false_ : node);
    cc

  let[@inline] find self n = N.find self.nstore n
  let[@inline] find_t self t : repr =
    let n = T_tbl.find self.tbl t in
    N.find self.nstore n

  let[@inline] check self acts : unit =
    Log.debug 5 "(cc.check)";
    self.new_merges <- false;
    update_tasks self acts

  let new_merges cc = cc.new_merges

  (* model: return all the classes *)
  let get_model (self:t) : repr Iter.t Iter.t =
    all_classes self |> Iter.map (N.iter_class self.nstore)
end
