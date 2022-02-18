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
       and type proof_step = A.proof_step
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
  type proof_step = A.proof_step
  type actions = Actions.t

  module Term = T.Term
  module Fun = T.Fun

  module Bits : sig
    type t = private int
    type field
    type bitfield_gen
    val empty : t
    val equal : t -> t -> bool
    val mk_field : bitfield_gen -> field
    val mk_gen : unit -> bitfield_gen
    val get : field -> t -> bool
    val set : field -> bool -> t -> t
    val merge : t -> t -> t
  end = struct
    type bitfield_gen = int ref
    let max_width = Sys.word_size - 2
    let mk_gen() = ref 0
    type t = int
    type field = int
    let empty : t = 0
    let mk_field (gen:bitfield_gen) : field =
      let n = !gen in
      if n > max_width then Error.errorf "maximum number of CC bitfields reached";
      incr gen;
      1 lsl n
    let[@inline] get field x = (x land field) <> 0
    let[@inline] set field b x =
      if b then x lor field else x land (lnot field)
    let merge = (lor)
    let equal : t -> t -> bool = CCEqual.poly
  end

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
    | E_trivial (* by pure reduction, tautologically equal *)
    | E_lit of lit (* because of this literal *)
    | E_merge of node * node
    | E_merge_t of term * term
    | E_congruence of node * node (* caused by normal congruence *)
    | E_and of explanation * explanation
    | E_theory of term * term * (term * term * explanation list) list * proof_step
    | E_same_val of node * node

  type repr = node

  module N = struct
    type t = node

    let[@inline] equal (n1:t) n2 = n1 == n2
    let[@inline] hash n = Term.hash n.n_term
    let[@inline] term n = n.n_term
    let[@inline] pp out n = Term.pp out n.n_term
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
      Bag.to_iter n.n_parents

    type bitfield = Bits.field
    let[@inline] get_field f t = Bits.get f t.n_bits
    let[@inline] set_field f b t = t.n_bits <- Bits.set f b t.n_bits
  end

  (* non-recursive, inlinable function for [find] *)
  let[@inline] find_ (n:node) : repr =
    let n2 = n.n_root in
    assert (N.is_root n2);
    n2

  let[@inline] same_class (n1:node)(n2:node): bool =
    N.equal (find_ n1) (find_ n2)

  let[@inline] find _ n = find_ n

  module Expl = struct
    type t = explanation

    let rec pp out (e:explanation) = match e with
      | E_trivial -> Fmt.string out "reduction"
      | E_lit lit -> Lit.pp out lit
      | E_congruence (n1,n2) -> Fmt.fprintf out "(@[congruence@ %a@ %a@])" N.pp n1 N.pp n2
      | E_merge (a,b) -> Fmt.fprintf out "(@[merge@ %a@ %a@])" N.pp a N.pp b
      | E_merge_t (a,b) ->
        Fmt.fprintf out "(@[<hv>merge@ @[:n1 %a@]@ @[:n2 %a@]@])" Term.pp a Term.pp b
      | E_theory (t,u,es,_) ->
        Fmt.fprintf out "(@[th@ :t `%a`@ :u `%a`@ :expl_sets %a@])"
          Term.pp t Term.pp u
          (Util.pp_list @@ Fmt.Dump.triple Term.pp Term.pp (Fmt.Dump.list pp)) es
      | E_and (a,b) ->
        Format.fprintf out "(@[<hv1>and@ %a@ %a@])" pp a pp b
      | E_same_val (n1,n2) ->
        Fmt.fprintf out "(@[same-value@ %a@ %a@])" N.pp n1 N.pp n2

    let mk_trivial : t = E_trivial
    let[@inline] mk_congruence n1 n2 : t = E_congruence (n1,n2)
    let[@inline] mk_merge a b : t = if N.equal a b then mk_trivial else E_merge (a,b)
    let[@inline] mk_merge_t a b : t = if Term.equal a b then mk_trivial else E_merge_t (a,b)
    let[@inline] mk_lit l : t = E_lit l
    let[@inline] mk_theory t u es pr = E_theory (t,u,es,pr)
    let[@inline] mk_same_value t u = if N.equal t u then mk_trivial else E_same_val (t,u)

    let rec mk_list l =
      match l with
      | [] -> mk_trivial
      | [x] -> x
      | E_trivial :: tl -> mk_list tl
      | x :: y ->
        match mk_list y with
        | E_trivial -> x
        | y' -> E_and (x,y')
  end

  module Resolved_expl = struct
    type t = {
      lits: lit list;
      same_value: (N.t * N.t) list;
      pr: proof -> proof_step;
    }

    let[@inline] is_semantic (self:t) : bool =
      match self.same_value with [] -> false | _::_ -> true

    let pp out (self:t) =
      if not (is_semantic self) then (
        Fmt.fprintf out "(@[resolved-expl@ %a@])" (Util.pp_list Lit.pp) self.lits
      ) else (
        let {lits; same_value; pr=_} = self in
        Fmt.fprintf out "(@[resolved-expl@ (@[%a@])@ :same-val (@[%a@])@])"
          (Util.pp_list Lit.pp) lits
          (Util.pp_list @@ Fmt.Dump.pair N.pp N.pp) same_value
      )
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

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list N.pp) l
      | App_ho (f, a) -> Fmt.fprintf out "(@[%a@ %a@])" N.pp f N.pp a
      | Opaque t -> N.pp out t
      | Not u -> Fmt.fprintf out "(@[not@ %a@])" N.pp u
      | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" N.pp a N.pp b
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" N.pp a N.pp b N.pp c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)
  module T_tbl = CCHashtbl.Make(Term)

  type combine_task =
    | CT_merge of node * node * explanation

  type t = {
    tst: term_store;
    tbl: node T_tbl.t;
    proof: proof;
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
    bitgen: Bits.bitfield_gen;
    field_marked_explain: Bits.field; (* used to mark traversed nodes when looking for a common ancestor *)
    true_ : node lazy_t;
    false_ : node lazy_t;
    stat: Stat.t;
    count_conflict: int Stat.counter;
    count_props: int Stat.counter;
    count_merge: int Stat.counter;
    count_semantic_conflict: int Stat.counter;
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
  and ev_on_propagate = t -> lit -> (unit -> lit list * proof_step) -> unit
  and ev_on_is_subterm = N.t -> term -> unit

  let[@inline] size_ (r:repr) = r.n_size
  let[@inline] n_true cc = Lazy.force cc.true_
  let[@inline] n_false cc = Lazy.force cc.false_
  let n_bool cc b = if b then n_true cc else n_false cc
  let[@inline] term_store cc = cc.tst
  let[@inline] proof cc = cc.proof
  let allocate_bitfield ~descr cc =
    Log.debugf 5 (fun k->k "(@[cc.allocate-bit-field@ :descr %s@])" descr);
    Bits.mk_field cc.bitgen

  let[@inline] on_backtrack cc f : unit =
    Backtrack_stack.push_if_nonzero_level cc.undo f

  let[@inline] get_bitfield _cc field n = N.get_field field n
  let set_bitfield cc field b n =
    let old = N.get_field field n in
    if old <> b then (
      on_backtrack cc (fun () -> N.set_field field old n);
      N.set_field field b n;
    )

  (* check if [t] is in the congruence closure.
     Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
  let[@inline] mem (cc:t) (t:term): bool = T_tbl.mem cc.tbl t

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
      Fmt.fprintf out "(@[%a%a%a%a@])" Term.pp n.n_term pp_root n pp_next n pp_expl n
    and pp_sig_e out (s,n) =
      Fmt.fprintf out "(@[<1>%a@ ~~> %a%a@])" Signature.pp s N.pp n pp_root n
    in
    Fmt.fprintf out
      "(@[@{<yellow>cc.state@}@ (@[<hv>:nodes@ %a@])@ (@[<hv>:sig-tbl@ %a@])@])"
      (Util.pp_iter ~sep:" " pp_n) (T_tbl.values cc.tbl)
      (Util.pp_iter ~sep:" " pp_sig_e) (Sig_tbl.to_iter cc.signatures_tbl)

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
    Log.debugf 50
      (fun k->k "(@[cc.add-sig@ %a@ ~~> %a@])" Signature.pp s N.pp n);
    on_backtrack cc (fun () -> Sig_tbl.remove cc.signatures_tbl s);
    Sig_tbl.add cc.signatures_tbl s n

  let push_pending cc t : unit =
    Log.debugf 50 (fun k->k "(@[<hv1>cc.push-pending@ %a@])" N.pp t);
    Vec.push cc.pending t

  let merge_classes cc t u e : unit =
    if t != u && not (same_class t u) then (
      Log.debugf 50
        (fun k->k "(@[<hv1>cc.push-combine@ %a ~@ %a@ :expl %a@])"
          N.pp t N.pp u Expl.pp e);
      Vec.push cc.combine @@ CT_merge (t,u,e)
    )

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

  let raise_conflict_ (cc:t) ~th (acts:actions) (e:lit list) (p:proof_step) : _ =
    Profile.instant "cc.conflict";
    (* clear tasks queue *)
    Vec.clear cc.pending;
    Vec.clear cc.combine;
    List.iter (fun f -> f cc ~th e) cc.on_conflict;
    Stat.incr cc.count_conflict;
    Actions.raise_conflict acts e p

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
  let find_common_ancestor cc (a:node) (b:node) : node =
    (* catch up to the other node *)
    let rec find1 a =
      if N.get_field cc.field_marked_explain a then a
      else (
        match a.n_expl with
        | FL_none -> assert false
        | FL_some r -> find1 r.next
      )
    in
    let rec find2 a b =
      if N.equal a b then a
      else if N.get_field cc.field_marked_explain a then a
      else if N.get_field cc.field_marked_explain b then b
      else (
        N.set_field cc.field_marked_explain true a;
        N.set_field cc.field_marked_explain true b;
        match a.n_expl, b.n_expl with
        | FL_some r1, FL_some r2 -> find2 r1.next r2.next
        | FL_some r, FL_none -> find1 r.next
        | FL_none, FL_some r -> find1 r.next
        | FL_none, FL_none -> assert false (* no common ancestor *)
      )

    in
    (* cleanup tags on nodes traversed in [find2] *)
    let rec cleanup_ n =
      if N.get_field cc.field_marked_explain n then (
        N.set_field cc.field_marked_explain false n;
        match n.n_expl with
        | FL_none -> ()
        | FL_some {next;_} -> cleanup_ next;
      )
    in
    let n = find2 a b in
    cleanup_ a;
    cleanup_ b;
    n

  module Expl_state = struct
    type t = {
      mutable lits: Lit.t list;
      mutable same_val: (N.t * N.t) list;
      mutable th_lemmas:
        (Lit.t * (Lit.t * Lit.t list) list * proof_step) list;
    }

    let create(): t = { lits=[]; same_val=[]; th_lemmas=[] }

    let[@inline] copy self : t = {self with lits=self.lits}
    let[@inline] add_lit (self:t) lit = self.lits <- lit :: self.lits
    let[@inline] add_th (self:t) lit hyps pr : unit =
      self.th_lemmas <- (lit,hyps,pr) :: self.th_lemmas
    let[@inline] add_same_val (self:t) n1 n2 : unit =
      self.same_val <- (n1,n2) :: self.same_val

    (** Does this explanation contain at least one merge caused by
        "same value"? *)
    let[@inline] is_semantic (self:t): bool = self.same_val <> []

    let merge self other =
      let {lits=o_lits; th_lemmas=o_lemmas;same_val=o_same_val} = other in
      self.lits <- List.rev_append o_lits self.lits;
      self.th_lemmas <- List.rev_append o_lemmas self.th_lemmas;
      self.same_val <- List.rev_append o_same_val self.same_val;
      ()

    (* proof of [\/_i ¬lits[i]] *)
    let proof_of_th_lemmas (self:t) (proof:proof) : proof_step =
      let p_lits1 = Iter.of_list self.lits |> Iter.map Lit.neg in
      let p_lits2 =
        Iter.of_list self.th_lemmas
        |> Iter.map (fun (lit_t_u,_,_) -> Lit.neg lit_t_u)
      in
      let p_cc = P.lemma_cc (Iter.append p_lits1 p_lits2) proof in
      let resolve_with_th_proof pr (lit_t_u,sub_proofs,pr_th) =
        (* pr_th: [sub_proofs |- t=u].
              now resolve away [sub_proofs] to get literals that were
              asserted in the congruence closure *)
        let pr_th = List.fold_left
            (fun pr_th (lit_i,hyps_i) ->
               (* [hyps_i |- lit_i] *)
               let lemma_i =
                 P.lemma_cc Iter.(cons lit_i (of_list hyps_i |> map Lit.neg)) proof
               in
               (* resolve [lit_i] away. *)
               P.proof_res ~pivot:(Lit.term lit_i) lemma_i pr_th proof)
            pr_th sub_proofs
        in
        P.proof_res ~pivot:(Lit.term lit_t_u) pr_th pr proof
      in
      (* resolve with theory proofs responsible for some merges, if any. *)
      List.fold_left resolve_with_th_proof p_cc self.th_lemmas

    let to_resolved_expl (self:t) : Resolved_expl.t =
      (* FIXME: package the th lemmas too *)
      let {lits; same_val; th_lemmas=_} = self in
      let s2 = copy self in
      let pr proof = proof_of_th_lemmas s2 proof in
      {Resolved_expl.lits; same_value=same_val; pr}
  end

  (* decompose explanation [e] into a list of literals added to [acc] *)
  let rec explain_decompose_expl cc (st:Expl_state.t) (e:explanation) : unit =
    Log.debugf 5 (fun k->k "(@[cc.decompose_expl@ %a@])" Expl.pp e);
    match e with
    | E_trivial -> ()
    | E_congruence (n1, n2) ->
      begin match n1.n_sig0, n2.n_sig0 with
        | Some (App_fun (f1, a1)), Some (App_fun (f2, a2)) ->
          assert (Fun.equal f1 f2);
          assert (List.length a1 = List.length a2);
          List.iter2 (explain_equal_rec_ cc st) a1 a2
        | Some (App_ho (f1, a1)), Some (App_ho (f2, a2)) ->
          explain_equal_rec_ cc st f1 f2;
          explain_equal_rec_ cc st a1 a2
        | Some (If (a1,b1,c1)), Some (If (a2,b2,c2)) ->
          explain_equal_rec_ cc st a1 a2;
          explain_equal_rec_ cc st b1 b2;
          explain_equal_rec_ cc st c1 c2;
        | _ ->
          assert false
      end
    | E_lit lit -> Expl_state.add_lit st lit
    | E_same_val (n1, n2) -> Expl_state.add_same_val st n1 n2
    | E_theory (t, u, expl_sets, pr) ->
      let sub_proofs =
        List.map
          (fun (t_i,u_i,expls_i) ->
             let lit_i = A.mk_lit_eq cc.tst t_i u_i in
             (* use a separate call to [explain_expls] for each set *)
             let sub = explain_expls cc expls_i in
             Expl_state.merge st sub;
             lit_i, sub.lits)
          expl_sets
      in
      let lit_t_u = A.mk_lit_eq cc.tst t u in
      Expl_state.add_th st lit_t_u sub_proofs pr
    | E_merge (a,b) -> explain_equal_rec_ cc st a b
    | E_merge_t (a,b) ->
      (* find nodes for [a] and [b] on the fly *)
      begin match T_tbl.find cc.tbl a, T_tbl.find cc.tbl b with
        | a, b -> explain_equal_rec_ cc st a b
        | exception Not_found ->
          Error.errorf "expl: cannot find node(s) for %a, %a" Term.pp a Term.pp b
      end
    | E_and (a,b) ->
      explain_decompose_expl cc st a;
      explain_decompose_expl cc st b

  and explain_expls cc (es:explanation list) : Expl_state.t =
    let st = Expl_state.create() in
    List.iter (explain_decompose_expl cc st) es;
    st

  and explain_equal_rec_ (cc:t) (st:Expl_state.t) (a:node) (b:node) : unit =
    Log.debugf 5
      (fun k->k "(@[cc.explain_loop.at@ %a@ =?= %a@])" N.pp a N.pp b);
    assert (N.equal (find_ a) (find_ b));
    let ancestor = find_common_ancestor cc a b in
    explain_along_path cc st a ancestor;
    explain_along_path cc st b ancestor

  (* explain why [a = parent_a], where [a -> ... -> target] in the
     proof forest *)
  and explain_along_path cc (st:Expl_state.t) (a:node) (target:node) : unit =
    let rec aux n =
      if n == target then ()
      else (
        match n.n_expl with
        | FL_none -> assert false
        | FL_some {next=next_n; expl=expl} ->
          explain_decompose_expl cc st expl;
          (* now prove [next_n = target] *)
          aux next_n
      )
    in aux a

  (* add a term *)
  let [@inline] rec add_term_rec_ cc t : node =
    try T_tbl.find cc.tbl t
    with Not_found -> add_new_term_ cc t

  (* add [t] to [cc] when not present already *)
  and add_new_term_ cc (t:term) : node =
    assert (not @@ mem cc t);
    Log.debugf 15 (fun k->k "(@[cc.add-term@ %a@])" Term.pp t);
    let n = N.make t in
    (* register sub-terms, add [t] to their parent list, and return the
       corresponding initial signature *)
    let sig0 = compute_sig0 cc n in
    n.n_sig0 <- sig0;
    (* remove term when we backtrack *)
    on_backtrack cc
      (fun () ->
         Log.debugf 15 (fun k->k "(@[cc.remove-term@ %a@])" Term.pp t);
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
        if Bag.is_empty old_parents then (
          (* first time it has parents: tell watchers that this is a subterm *)
          List.iter (fun f -> f sub u) self.on_is_subterm;
        );
        on_backtrack self (fun () -> sub_r.n_parents <- old_parents);
        sub_r.n_parents <- Bag.cons n sub_r.n_parents;
      end;
      sub
    in
    let[@inline] return x = Some x in
    match A.cc_view n.n_term with
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
    | App_ho (f, a ) ->
      let f = deref_sub f in
      let a = deref_sub a in
      return @@ App_ho (f, a)
    | If (a,b,c) ->
      return @@ If (deref_sub a, deref_sub b, deref_sub c)

  let[@inline] add_term cc t : node = add_term_rec_ cc t

  let mem_term = mem

  let set_as_lit cc (n:node) (lit:lit) : unit =
    match n.n_as_lit with
    | Some _ -> ()
    | None ->
      Log.debugf 15 (fun k->k "(@[cc.set-as-lit@ %a@ %a@])" N.pp n Lit.pp lit);
      on_backtrack cc (fun () -> n.n_as_lit <- None);
      n.n_as_lit <- Some lit

  (* is [n] true or false? *)
  let n_is_bool_value (self:t) n : bool =
    N.equal n (n_true self) || N.equal n (n_false self)

  (* gather a pair [lits, pr], where [lits] is the set of
     asserted literals needed in the explanation (which is useful for
     the SAT solver), and [pr] is a proof, including sub-proofs for theory
     merges. *)
  let lits_and_proof_of_expl
      (self:t) (st:Expl_state.t) : Lit.t list * proof_step =
    let {Expl_state.lits; th_lemmas=_; same_val} = st in
    assert (same_val = []);
    let pr = Expl_state.proof_of_th_lemmas st self.proof in
    lits, pr

  (* main CC algo: add terms from [pending] to the signature table,
     check for collisions *)
  let rec update_tasks (cc:t) (acts:actions) : unit =
    while not (Vec.is_empty cc.pending && Vec.is_empty cc.combine) do
      while not @@ Vec.is_empty cc.pending do
        task_pending_ cc (Vec.pop_exn cc.pending);
      done;
      while not @@ Vec.is_empty cc.combine do
        task_combine_ cc acts (Vec.pop_exn cc.combine);
      done;
    done

  and task_pending_ cc (n:node) : unit =
    (* check if some parent collided *)
    begin match n.n_sig0 with
      | None -> () (* no-op *)
      | Some (Eq (a,b)) ->
        (* if [a=b] is now true, merge [(a=b)] and [true] *)
        if same_class a b then (
          let expl = Expl.mk_merge a b in
          Log.debugf 5
            (fun k->k "(@[cc.pending.eq@ %a@ :r1 %a@ :r2 %a@])" N.pp n N.pp a N.pp b);
          merge_classes cc n (n_true cc) expl
        )
      | Some (Not u) ->
        (* [u = bool ==> not u = not bool] *)
        let r_u = find_ u in
        if N.equal r_u (n_true cc) then (
          let expl = Expl.mk_merge u (n_true cc) in
          merge_classes cc n (n_false cc) expl
        ) else if N.equal r_u (n_false cc) then (
          let expl = Expl.mk_merge u (n_false cc) in
          merge_classes cc n (n_true cc) expl
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
    | CT_merge (a,b,e_ab) ->
      cc.new_merges <- true;
      task_merge_ cc acts a b e_ab

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
      if (N.equal ra (n_true cc) && N.equal rb (n_false cc)) ||
         (N.equal rb (n_true cc) && N.equal ra (n_false cc)) then (
        Log.debugf 5
          (fun k->k "(@[<hv>cc.merge.true_false_conflict@ \
                     @[:r1 %a@ :t1 %a@]@ @[:r2 %a@ :t2 %a@]@ :e_ab %a@])"
            N.pp ra N.pp a N.pp rb N.pp b Expl.pp e_ab);
        let th = ref false in
        (* TODO:
           C1: P.true_neq_false
           C2: lemma [lits |- true=false]  (and resolve on theory proofs)
           C3: r1 C1 C2
        *)
        let expl_st = Expl_state.create() in
        explain_decompose_expl cc expl_st e_ab;
        explain_equal_rec_ cc expl_st a ra;
        explain_equal_rec_ cc expl_st b rb;

        if Expl_state.is_semantic expl_st then (
          (* conflict involving some semantic values *)
          let lits = expl_st.lits in
          let same_val =
            expl_st.same_val
            |> List.rev_map (fun (t,u) -> N.term t, N.term u) in
          assert (same_val <> []);
          Stat.incr cc.count_semantic_conflict;
          Actions.raise_semantic_conflict acts lits same_val

        ) else (
          (* regular conflict *)
          let lits, pr = lits_and_proof_of_expl cc expl_st in
          raise_conflict_ cc ~th:!th acts (List.rev_map Lit.neg lits) pr
        )
      );
      (* We will merge [r_from] into [r_into].
         we try to ensure that [size ra <= size rb] in general, but always
         keep values as representative *)
      let r_from, r_into =
        if n_is_bool_value cc ra then rb, ra
        else if n_is_bool_value cc rb then ra, rb
        else if size_ ra > size_ rb then rb, ra
        else ra, rb
      in
      (* when merging terms with [true] or [false], possibly propagate them to SAT *)
      let merge_bool r1 t1 r2 t2 =
        if N.equal r1 (n_true cc) then (
          propagate_bools cc acts r2 t2 r1 t1 e_ab true
        ) else if N.equal r1 (n_false cc) then (
          propagate_bools cc acts r2 t2 r1 t1 e_ab false
        )
      in
      merge_bool ra a rb b;
      merge_bool rb b ra a;
      (* perform [union r_from r_into] *)
      Log.debugf 15 (fun k->k "(@[cc.merge@ :from %a@ :into %a@])" N.pp r_from N.pp r_into);
      (* call [on_pre_merge] functions, and merge theory data items *)
      begin
        (* explanation is [a=ra & e_ab & b=rb] *)
        let expl = Expl.mk_list [e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb] in
        List.iter (fun f -> f cc acts r_into r_from expl) cc.on_pre_merge;
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
      (* call [on_post_merge] *)
      begin
        List.iter (fun f -> f cc acts r_into r_from) cc.on_post_merge;
      end;
    )

  (* we are merging [r1] with [r2==Bool(sign)], so propagate each term [u1]
     in the equiv class of [r1] that is a known literal back to the SAT solver
     and which is not the one initially merged.
     We can explain the propagation with [u1 = t1 =e= t2 = r2==bool] *)
  and propagate_bools cc acts r1 t1 r2 t2 (e_12:explanation) sign : unit =
    (* explanation for [t1 =e= t2 = r2] *)
    let half_expl_and_pr = lazy (
      let st = Expl_state.create() in
      explain_decompose_expl cc st e_12;
      explain_equal_rec_ cc st r2 t2;
      st
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
             let e = lazy (
               let lazy st = half_expl_and_pr in
               explain_equal_rec_ cc st u1 t1;
               (* true literals explaining why t1=t2 *)
               let guard = st.lits in
               (* get a proof of [guard /\ ¬lit] being absurd, to propagate [lit] *)
               let st = Expl_state.copy st in (* do not modify shared st *)
               Expl_state.add_lit st (Lit.neg lit);
               let _, pr = lits_and_proof_of_expl cc st in
               guard, pr
             ) in
             fun () -> Lazy.force e
           in
           List.iter (fun f -> f cc lit reason) cc.on_propagate;
           Stat.incr cc.count_props;
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
  let raise_conflict_from_expl cc (acts:actions) expl =
    Log.debugf 5
      (fun k->k "(@[cc.theory.raise-conflict@ :expl %a@])" Expl.pp expl);
    let st = Expl_state.create() in
    explain_decompose_expl cc st expl;
    let lits, pr = lits_and_proof_of_expl cc st in
    let c = List.rev_map Lit.neg lits in
    let th = st.th_lemmas <> [] in
    raise_conflict_ cc ~th acts c pr

  let merge cc n1 n2 expl =
    Log.debugf 5
      (fun k->k "(@[cc.theory.merge@ :n1 %a@ :n2 %a@ :expl %a@])" N.pp n1 N.pp n2 Expl.pp expl);
    assert (T.Ty.equal (T.Term.ty n1.n_term) (T.Term.ty n2.n_term));
    merge_classes cc n1 n2 expl

  let[@inline] merge_t cc t1 t2 expl =
    merge cc (add_term cc t1) (add_term cc t2) expl

  let merge_same_value cc n1 n2 = merge cc n1 n2 (Expl.mk_same_value n1 n2)
  let merge_same_value_t cc t1 t2 = merge_same_value cc (add_term cc t1) (add_term cc t2)

  let explain_eq cc n1 n2 : Resolved_expl.t =
    let st = Expl_state.create() in
    explain_equal_rec_ cc st n1 n2;
    (* FIXME: also need to return the proof? *)
    Expl_state.to_resolved_expl st

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
      (tst:term_store) (proof:proof) : t =
    let size = match size with `Small -> 128 | `Big -> 2048 in
    let bitgen = Bits.mk_gen () in
    let field_marked_explain = Bits.mk_field bitgen in
    let rec cc = {
      tst; proof;
      tbl = T_tbl.create size;
      signatures_tbl = Sig_tbl.create size;
      bitgen;
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
      count_semantic_conflict=Stat.mk_int stat "cc.semantic-conflicts";
    } and true_ = lazy (
        add_term cc (Term.bool tst true)
      ) and false_ = lazy (
        add_term cc (Term.bool tst false)
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
    cc.new_merges <- false;
    update_tasks cc acts

  let new_merges cc = cc.new_merges

  let check_inv_enabled_ = true (* XXX NUDGE *)

  (* check some internal invariants *)
  let check_inv_ (self:t) : unit =
    if check_inv_enabled_ then (
      Log.debug 2 "(cc.check-invariants)";
      all_classes self
      |> Iter.flat_map N.iter_class
      |> Iter.iter
        (fun n ->
           match n.n_sig0 with
           | None -> ()
           | Some s ->
             let s' = update_sig s in
             let ok = match find_signature self s' with
               | None -> false
               | Some r -> N.equal r n.n_root
             in
             if not ok then (
               Log.debugf 0
                 (fun k->k "(@[cc.check.fail@ :n %a@ :sig %a@ :actual-sig %a@])"
                     N.pp n Signature.pp s Signature.pp s')
             )
        )
    )

  (* model: return all the classes *)
  let get_model (cc:t) : repr Iter.t Iter.t =
    check_inv_ cc;
    all_classes cc |> Iter.map N.iter_class
end
