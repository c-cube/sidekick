
open CC_types

module type ARG = Congruence_closure_intf.ARG
module type S = Congruence_closure_intf.S

module Bits = CCBitField.Make()

let field_is_pending = Bits.mk_field()
(** true iff the node is in the [cc.pending] queue *)

let () = Bits.freeze()

type payload = Congruence_closure_intf.payload = ..

module Make(A: ARG) = struct
  type term = A.Term.t
  type term_state = A.Term.state
  type lit = A.Lit.t
  type fun_ = A.Fun.t
  type proof = A.Proof.t
  type value = A.Value.t
  type model = A.Model.t

  (** Actions available to the theory *)
  type sat_actions = (Msat.void, lit, Msat.void, proof) Msat.acts

  module T = A.Term
  module Fun = A.Fun

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
    mutable n_as_lit: lit option;
    mutable n_expl: explanation_forest_link; (* the rooted forest for explanations *)
    mutable n_payload: payload list; (* list of theory payloads *)
    (* TODO: make a micro theory and move this inside *)
    mutable n_tags: (node * explanation) Util.Int_map.t;
    (* "distinct" tags (i.e. set of `(distinct t1…tn)` terms this belongs to *)
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
    | E_merges of (node * node) list (* caused by these merges *)
    | E_lit of lit (* because of this literal *)
    | E_lits of lit list (* because of this (true) conjunction *)
  (* TODO: congruence case (cheaper than "merges") *)

  type repr = node
  type conflict = lit list

  module N = struct
    type t = node

    let[@inline] equal (n1:t) n2 = T.equal n1.n_term n2.n_term
    let[@inline] hash n = T.hash n.n_term
    let[@inline] term n = n.n_term
    let[@inline] payload n = n.n_payload
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
        n_payload=[];
        n_next=n;
        n_size=1;
        n_tags=Util.Int_map.empty;
      } in
      n

    let[@inline] is_root (n:node) : bool = n.n_root == n

    (* traverse the equivalence class of [n] *)
    let iter_class_ (n:node) : node Sequence.t =
      fun yield ->
        let rec aux u =
          yield u;
          if u.n_next != n then aux u.n_next
        in
        aux n

    let iter_class n =
      assert (is_root n);
      iter_class_ n

    let[@inline] iter_parents (n:node) : node Sequence.t =
      assert (is_root n);
      Bag.to_seq n.n_parents

    type nonrec payload = payload = ..

    let set_payload ?(can_erase=fun _->false) n e =
      let rec aux = function
        | [] -> [e]
        | e' :: tail when can_erase e' -> e :: tail
        | e' :: tail -> e' :: aux tail
      in
      n.n_payload <- aux n.n_payload

    let payload_find ~f:p n =
      let[@unroll 2] rec aux = function
        | [] -> None
        | e1 :: tail ->
          match p e1 with
          | Some _ as res -> res
          | None -> aux tail
      in
      aux n.n_payload

    let payload_pred ~f:p n =
      begin match n.n_payload with
        | [] -> false
        | e :: _ when p e -> true
        | _ :: e :: _ when p e -> true
        | _ :: _ :: e :: _ when p e -> true
        | l -> List.exists p l
      end

    let[@inline] get_field f t = Bits.get f t.n_bits
    let[@inline] set_field f b t = t.n_bits <- Bits.set f b t.n_bits
  end

  module N_tbl = CCHashtbl.Make(N)

  module Expl = struct
    type t = explanation

    let equal (a:t) b =
      match a, b with
      | E_merges l1, E_merges l2 ->
        CCList.equal (CCPair.equal N.equal N.equal) l1 l2
      | E_reduction, E_reduction -> true
      | E_lit l1, E_lit l2 -> A.Lit.equal l1 l2
      | E_lits l1, E_lits l2 -> CCList.equal A.Lit.equal l1 l2
      | E_merges _, _ | E_lit _, _ | E_lits _, _ | E_reduction, _
        -> false

    let hash (a:t) : int =
      let module H = CCHash in
      match a with
      | E_lit lit -> H.combine2 10 (A.Lit.hash lit)
      | E_lits l ->
        H.combine2 20 (H.list A.Lit.hash l)
      | E_merges l ->
        H.combine2 30 (H.list (H.pair N.hash N.hash) l)
      | E_reduction -> H.int 40

    let pp out (e:explanation) = match e with
      | E_reduction -> Fmt.string out "reduction"
      | E_lit lit -> A.Lit.pp out lit
      | E_lits l -> CCFormat.Dump.list A.Lit.pp out l
      | E_merges l ->
        Format.fprintf out "(@[<hv1>merges@ %a@])"
          Fmt.(seq ~sep:(return "@ ") @@ within "[" "]" @@ hvbox @@
            pair ~sep:(return " ~@ ") N.pp N.pp)
          (Sequence.of_list l)

    let[@inline] mk_merges l : t = E_merges l
    let[@inline] mk_lit l : t = E_lit l
    let[@inline] mk_lits = function [x] -> mk_lit x | l -> E_lits l
    let mk_reduction : t = E_reduction
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
      | If (a1,b1,c1), If (a2,b2,c2) ->
        N.equal a1 a2 && N.equal b1 b2 && N.equal c1 c2
      | Eq (a1,b1), Eq (a2,b2) ->
        N.equal a1 a2 && N.equal b1 b2
      | Opaque u1, Opaque u2 -> N.equal u1 u2
      | Bool _, _ | App_fun _, _ | App_ho _, _ | If _, _
      | Eq _, _ | Opaque _, _
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

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list N.pp) l
      | App_ho (f, []) -> N.pp out f
      | App_ho (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" N.pp f (Util.pp_list N.pp) l
      | Opaque t -> N.pp out t
      | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" N.pp a N.pp b
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" N.pp a N.pp b N.pp c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)
  module T_tbl = CCHashtbl.Make(T)

  type combine_task =
    | CT_merge of node * node * explanation
    | CT_distinct of node list * int * explanation

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
    on_merge: (repr -> repr -> explanation -> unit) option;
    mutable ps_lits: lit list; (* TODO: thread it around instead? *)
    (* proof state *)
    ps_queue: (node*node) Vec.t;
    (* pairs to explain *)
    true_ : node lazy_t;
    false_ : node lazy_t;
  }
  (* TODO: an additional union-find to keep track, for each term,
     of the terms they are known to be equal to, according
     to the current explanation. That allows not to prove some equality
     several times.
     See "fast congruence closure and extensions", Nieuwenhis&al, page 14 *)

  let[@inline] size_ (r:repr) = r.n_size
  let[@inline] true_ cc = Lazy.force cc.true_
  let[@inline] false_ cc = Lazy.force cc.false_

  let[@inline] on_backtrack cc f : unit =
    Backtrack_stack.push_if_nonzero_level cc.undo f

  (* check if [t] is in the congruence closure.
     Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
  let[@inline] mem (cc:t) (t:term): bool = T_tbl.mem cc.tbl t

  (* find representative, recursively *)
  let[@unroll 1] rec find_rec (n:node) : repr =
    if n==n.n_root then (
      n
    ) else (
      (* TODO: path compression, assuming backtracking restores equiv classes
         properly *)
      let root = find_rec n.n_root in
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
    CC_types.map_view s
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

  let push_combine cc t u e : unit =
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
    acts.Msat.acts_raise_conflict c A.Proof.default

  let[@inline] all_classes cc : repr Sequence.t =
    T_tbl.values cc.tbl
    |> Sequence.filter N.is_root

  (* TODO: use markers and lockstep iteration instead *)
  (* distance from [t] to its root in the proof forest *)
  let[@inline][@unroll 2] rec distance_to_root (n:node): int = match n.n_expl with
    | FL_none -> 0
    | FL_some {next=t'; _} -> 1 + distance_to_root t'

  (* TODO: bool flag on nodes +  stepwise progress + cleanup *)
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

  (* TODO: remove *)
  let ps_clear (cc:t) =
    cc.ps_lits <- [];
    Vec.clear cc.ps_queue;
    ()

  let decompose_explain cc (e:explanation): unit =
    Log.debugf 5 (fun k->k "(@[cc.decompose_expl@ %a@])" Expl.pp e);
    begin match e with
      | E_reduction -> ()
      | E_lit lit -> ps_add_lit cc lit
      | E_lits l -> List.iter (ps_add_lit cc) l
      | E_merges l ->
        (* need to explain each merge in [l] *)
        List.iter (fun (t,u) -> ps_add_obligation cc t u) l
    end

  (* explain why [a = parent_a], where [a -> ... -> parent_a] in the
     proof forest *)
  let rec explain_along_path ps (a:node) (parent_a:node) : unit =
    if a!=parent_a then (
      match a.n_expl with
        | FL_none -> assert false
        | FL_some {next=next_a; expl=e_a_b} ->
          decompose_explain ps e_a_b;
          (* now prove [next_a = parent_a] *)
          explain_along_path ps next_a parent_a
    )

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

  (* TODO: do not use ps_lits anymore *)
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

  (* add [tag] to [n], indicating that [n] is distinct from all the other
     nodes tagged with [tag]
     precond: [n] is a representative *)
  let add_tag_n cc (n:node) (tag:int) (expl:explanation) : unit =
    assert (N.is_root n);
    if not (Util.Int_map.mem tag n.n_tags) then (
      on_backtrack cc
        (fun () -> n.n_tags <- Util.Int_map.remove tag n.n_tags);
      n.n_tags <- Util.Int_map.add tag (n,expl) n.n_tags;
    )

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
    | App_fun (f, args) ->
      let args = args |> Sequence.map deref_sub |> Sequence.to_list in
      if args<>[] then (
        return @@ App_fun (f, args)
      ) else None
    | App_ho (f, args) ->
      let args = args |> Sequence.map deref_sub |> Sequence.to_list in
      return @@ App_ho (deref_sub f, args)
    | If (a,b,c) ->
      return @@ If (deref_sub a, deref_sub b, deref_sub c)

  let[@inline] add_term cc t : node = add_term_rec_ cc t
  let[@inline] add_term' cc t : unit = ignore (add_term_rec_ cc t : node)

  let set_as_lit cc (n:node) (lit:lit) : unit =
    match n.n_as_lit with
    | Some _ -> ()
    | None ->
      Log.debugf 15 (fun k->k "(@[cc.set-as-lit@ %a@ %a@])" N.pp n A.Lit.pp lit);
      on_backtrack cc (fun () -> n.n_as_lit <- None);
      n.n_as_lit <- Some lit

  (* Checks if [ra] and [~into] have compatible normal forms and can
     be merged w.r.t. the theories.
     Side effect: also pushes sub-tasks *)
  let notify_merge cc (ra:repr) ~into:(rb:repr) (e:explanation): unit =
    assert (N.is_root rb);
    match cc.on_merge with
    | Some f -> f ra rb e
    | None -> ()

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
          let expl = Expl.mk_merges [(a,b)] in
          push_combine cc n (true_ cc) expl
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
          let expl =
            match n.n_sig0, u.n_sig0 with
            | Some (App_fun (f1, a1)), Some (App_fun (f2, a2)) ->
              assert (Fun.equal f1 f2);
              assert (List.length a1 = List.length a2);
              (* TODO: just use "congruence" as explanation *)
              Expl.mk_merges @@ List.combine a1 a2
            | Some (App_ho (f1, a1)), Some (App_ho (f2, a2)) ->
              assert (List.length a1 = List.length a2);
              (* TODO: just use "congruence" as explanation *)
              Expl.mk_merges @@ (f1,f2)::List.combine a1 a2
            | Some (If (a1,b1,c1)), Some (If (a2,b2,c2)) ->
              Expl.mk_merges @@ [a1,a2; b1,b2; c1,c2]
            | _
              -> assert false
          in
          push_combine cc n u expl
      (* FIXME: when to actually evaluate?
         eval_pending cc;
      *)
    end

  and[@inline] task_combine_ cc acts = function
    | CT_merge (a,b,e_ab) -> task_merge_ cc acts a b e_ab
    | CT_distinct (l,tag,e) -> task_distinct_ cc acts l tag e

  (* main CC algo: merge equivalence classes in [st.combine].
     @raise Exn_unsat if merge fails *)
  and task_merge_ cc acts a b e_ab : unit =
    let ra = find_ a in
    let rb = find_ b in
    if not @@ N.equal ra rb then (
      assert (N.is_root ra);
      assert (N.is_root rb);
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
      (* TODO: instead call micro theories, including "distinct" *)
      (* update set of tags the new node cannot be equal to *)
      let new_tags =
        Util.Int_map.union
          (fun _i (n1,e1) (n2,e2) ->
             (* both maps contain same tag [_i]. conflict clause:
                 [e1 & e2 & e_ab] impossible *)
             Log.debugf 5
               (fun k->k "(@[<hv>cc.merge.distinct_conflict@ :tag %d@ \
                          @[:r1 %a@ :e1 %a@]@ @[:r2 %a@ :e2 %a@]@ :e_ab %a@])"
                   _i N.pp n1 Expl.pp e1
                   N.pp n2 Expl.pp e2 Expl.pp e_ab);
             let lits = explain_unfold cc e1 in
             let lits = explain_unfold ~init:lits cc e2 in
             let lits = explain_unfold ~init:lits cc e_ab in
             let lits = explain_eq_n ~init:lits cc a n1 in
             let lits = explain_eq_n ~init:lits cc b n2 in
             raise_conflict cc acts lits)
          ra.n_tags rb.n_tags
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
        let r_into_old_tags = r_into.n_tags in
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
             r_into.n_tags <- r_into_old_tags;
             r_into.n_parents <- r_into_old_parents;
             N.iter_class_ r_from (fun u -> u.n_root <- r_from);
          );
        r_into.n_tags <- new_tags;
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
      (* notify listeners of the merge *)
      notify_merge cc r_from ~into:r_into e_ab;
    )

  and task_distinct_ cc acts (l:node list) tag expl : unit =
    let l = List.map (fun n -> n, find_ n) l in
    let coll =
      Sequence.diagonal_l l
      |> Sequence.find_pred (fun ((_,r1),(_,r2)) -> N.equal r1 r2)
    in
    begin match coll with
      | Some ((n1,_r1),(n2,_r2)) ->
        (* two classes are already equal *)
        Log.debugf 5
          (fun k->k "(@[cc.distinct.conflict@ %a = %a@ :expl %a@])" N.pp n1 N.pp
              n2 Expl.pp expl);
        let lits = explain_unfold cc expl in
        raise_conflict cc acts lits
      | None ->
        (* put a tag on all equivalence classes, that will make their merge fail *)
        List.iter (fun (_,n) -> add_tag_n cc n tag expl) l
    end

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
           let expl = explain_eq_n ~init:(Lazy.force half_expl) cc u1 t1 in
           let reason = Msat.Consequence (expl, A.Proof.default) in
           acts.Msat.acts_propagate lit reason
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
     if it's [distinct a1…an], make them distinct, etc. etc. *)
  let assert_lit cc lit : unit =
    let t = A.Lit.term lit in
    Log.debugf 5 (fun k->k "(@[cc.assert_lit@ %a@])" A.Lit.pp lit);
    let sign = A.Lit.sign lit in
    begin match T.cc_view t with
      | Eq (a,b) when sign ->
        (* merge [a] and [b] *)
        let a = add_term cc a in
        let b = add_term cc b in
        push_combine cc a b (Expl.mk_lit lit)
      | _ ->
        (* equate t and true/false *)
        let rhs = if sign then true_ cc else false_ cc in
        let n = add_term cc t in
        (* TODO: ensure that this is O(1).
           basically, just have [n] point to true/false and thus acquire
           the corresponding value, so its superterms (like [ite]) can evaluate
           properly *)
        push_combine cc n rhs (Expl.mk_lit lit)
    end

  let[@inline] assert_lits cc lits : unit =
    Sequence.iter (assert_lit cc) lits

  let assert_eq cc t1 t2 (e:lit list) : unit =
    let expl = Expl.mk_lits e in
    let n1 = add_term cc t1 in
    let n2 = add_term cc t2 in
    push_combine cc n1 n2 expl

  (* generative tag used to annotate classes that can't be merged *)
  let distinct_tag_ = ref 0

  let assert_distinct cc (l:term list) ~neq:_ (lit:lit) : unit =
    assert (match l with[] | [_] -> false | _ -> true);
    let tag = CCRef.get_then_incr distinct_tag_ in
    Log.debugf 5
      (fun k->k "(@[cc.assert_distinct@ (@[%a@])@ :tag %d@])" (Util.pp_list T.pp) l tag);
    let l = List.map (add_term cc) l in
    Vec.push cc.combine @@ CT_distinct (l, tag, Expl.mk_lit lit)

  let create ?on_merge ?(size=`Big) (tst:term_state) : t =
    let size = match size with `Small -> 128 | `Big -> 2048 in
    let rec cc = {
      tst;
      tbl = T_tbl.create size;
      signatures_tbl = Sig_tbl.create size;
      on_merge;
      pending=Vec.create();
      combine=Vec.create();
      ps_lits=[];
      undo=Backtrack_stack.create();
      ps_queue=Vec.create();
      true_;
      false_;
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
             |> Sequence.find_map (fun n -> Model.eval m n.n_term)
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
      |> Sequence.map
        (fun n ->
           let r = find_ n in
           let v =
             try N_tbl.find t_tbl r
             with Not_found ->
               Error.errorf "didn't allocate a value for repr %a" N.pp r
           in
           n.n_term, v)
    in
    let m = Sequence.fold (fun m (t,v) -> Model.add t v m) m pairs in
    Log.debugf 5 (fun k->k "(@[cc.model@ %a@])" Model.pp m);
    m
end
