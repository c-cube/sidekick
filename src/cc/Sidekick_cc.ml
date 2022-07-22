open Sidekick_sigs_cc
module View = View
open View

module type S = sig
  include S

  val create :
    ?stat:Stat.t -> ?size:[ `Small | `Big ] -> term_store -> proof_trace -> t
  (** Create a new congruence closure.

      @param term_store used to be able to create new terms. All terms
      interacting with this congruence closure must belong in this term state
      as well.
  *)

  (**/**)

  module Debug_ : sig
    val pp : t Fmt.printer
    (** Print the whole CC *)
  end

  (**/**)
end

module type ARG = ARG

(* small bitfield *)
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
  let mk_gen () = ref 0

  type t = int
  type field = int

  let empty : t = 0

  let mk_field (gen : bitfield_gen) : field =
    let n = !gen in
    if n > max_width then Error.errorf "maximum number of CC bitfields reached";
    incr gen;
    1 lsl n

  let[@inline] get field x = x land field <> 0

  let[@inline] set field b x =
    if b then
      x lor field
    else
      x land lnot field

  let merge = ( lor )
  let equal : t -> t -> bool = CCEqual.poly
end

module Make (A : ARG) :
  S
    with module T = A.T
     and module Lit = A.Lit
     and module Proof_trace = A.Proof_trace = struct
  module T = A.T
  module Lit = A.Lit
  module Proof_trace = A.Proof_trace
  module Term = T.Term
  module Fun = T.Fun

  open struct
    (* proof rules *)
    module Rules_ = A.Rule_core
    module P = Proof_trace
  end

  type term = T.Term.t
  type value = term
  type term_store = T.Term.store
  type lit = Lit.t
  type fun_ = T.Fun.t
  type proof_trace = A.Proof_trace.t
  type step_id = A.Proof_trace.A.step_id

  type e_node = {
    n_term: term;
    mutable n_sig0: signature option; (* initial signature *)
    mutable n_bits: Bits.t; (* bitfield for various properties *)
    mutable n_parents: e_node Bag.t; (* parent terms of this node *)
    mutable n_root: e_node;
    (* representative of congruence class (itself if a representative) *)
    mutable n_next: e_node; (* pointer to next element of congruence class *)
    mutable n_size: int; (* size of the class *)
    mutable n_as_lit: lit option;
    (* TODO: put into payload? and only in root? *)
    mutable n_expl: explanation_forest_link;
        (* the rooted forest for explanations *)
  }
  (** A node of the congruence closure.
      An equivalence class is represented by its "root" element,
      the representative. *)

  and signature = (fun_, e_node, e_node list) View.t

  and explanation_forest_link =
    | FL_none
    | FL_some of { next: e_node; expl: explanation }

  (* atomic explanation in the congruence closure *)
  and explanation =
    | E_trivial (* by pure reduction, tautologically equal *)
    | E_lit of lit (* because of this literal *)
    | E_merge of e_node * e_node
    | E_merge_t of term * term
    | E_congruence of e_node * e_node (* caused by normal congruence *)
    | E_and of explanation * explanation
    | E_theory of term * term * (term * term * explanation list) list * step_id
    | E_same_val of e_node * e_node

  type repr = e_node

  module E_node = struct
    type t = e_node

    let[@inline] equal (n1 : t) n2 = n1 == n2
    let[@inline] hash n = Term.hash n.n_term
    let[@inline] term n = n.n_term
    let[@inline] pp out n = Term.pp out n.n_term
    let[@inline] as_lit n = n.n_as_lit

    let make (t : term) : t =
      let rec n =
        {
          n_term = t;
          n_sig0 = None;
          n_bits = Bits.empty;
          n_parents = Bag.empty;
          n_as_lit = None;
          (* TODO: provide a method to do it *)
          n_root = n;
          n_expl = FL_none;
          n_next = n;
          n_size = 1;
        }
      in
      n

    let[@inline] is_root (n : e_node) : bool = n.n_root == n

    (* traverse the equivalence class of [n] *)
    let iter_class_ (n : e_node) : e_node Iter.t =
     fun yield ->
      let rec aux u =
        yield u;
        if u.n_next != n then aux u.n_next
      in
      aux n

    let[@inline] iter_class n =
      assert (is_root n);
      iter_class_ n

    let[@inline] iter_parents (n : e_node) : e_node Iter.t =
      assert (is_root n);
      Bag.to_iter n.n_parents

    type bitfield = Bits.field

    let[@inline] get_field f t = Bits.get f t.n_bits
    let[@inline] set_field f b t = t.n_bits <- Bits.set f b t.n_bits
  end

  (* non-recursive, inlinable function for [find] *)
  let[@inline] find_ (n : e_node) : repr =
    let n2 = n.n_root in
    assert (E_node.is_root n2);
    n2

  let[@inline] same_class (n1 : e_node) (n2 : e_node) : bool =
    E_node.equal (find_ n1) (find_ n2)

  let[@inline] find _ n = find_ n

  module Expl = struct
    type t = explanation

    let rec pp out (e : explanation) =
      match e with
      | E_trivial -> Fmt.string out "reduction"
      | E_lit lit -> Lit.pp out lit
      | E_congruence (n1, n2) ->
        Fmt.fprintf out "(@[congruence@ %a@ %a@])" E_node.pp n1 E_node.pp n2
      | E_merge (a, b) ->
        Fmt.fprintf out "(@[merge@ %a@ %a@])" E_node.pp a E_node.pp b
      | E_merge_t (a, b) ->
        Fmt.fprintf out "(@[<hv>merge@ @[:n1 %a@]@ @[:n2 %a@]@])" Term.pp a
          Term.pp b
      | E_theory (t, u, es, _) ->
        Fmt.fprintf out "(@[th@ :t `%a`@ :u `%a`@ :expl_sets %a@])" Term.pp t
          Term.pp u
          (Util.pp_list @@ Fmt.Dump.triple Term.pp Term.pp (Fmt.Dump.list pp))
          es
      | E_and (a, b) -> Format.fprintf out "(@[<hv1>and@ %a@ %a@])" pp a pp b
      | E_same_val (n1, n2) ->
        Fmt.fprintf out "(@[same-value@ %a@ %a@])" E_node.pp n1 E_node.pp n2

    let mk_trivial : t = E_trivial
    let[@inline] mk_congruence n1 n2 : t = E_congruence (n1, n2)

    let[@inline] mk_merge a b : t =
      if E_node.equal a b then
        mk_trivial
      else
        E_merge (a, b)

    let[@inline] mk_merge_t a b : t =
      if Term.equal a b then
        mk_trivial
      else
        E_merge_t (a, b)

    let[@inline] mk_lit l : t = E_lit l
    let[@inline] mk_theory t u es pr = E_theory (t, u, es, pr)

    let[@inline] mk_same_value t u =
      if E_node.equal t u then
        mk_trivial
      else
        E_same_val (t, u)

    let rec mk_list l =
      match l with
      | [] -> mk_trivial
      | [ x ] -> x
      | E_trivial :: tl -> mk_list tl
      | x :: y ->
        (match mk_list y with
        | E_trivial -> x
        | y' -> E_and (x, y'))
  end

  module Resolved_expl = struct
    type t = {
      lits: lit list;
      same_value: (E_node.t * E_node.t) list;
      pr: proof_trace -> step_id;
    }

    let[@inline] is_semantic (self : t) : bool =
      match self.same_value with
      | [] -> false
      | _ :: _ -> true

    let pp out (self : t) =
      if not (is_semantic self) then
        Fmt.fprintf out "(@[resolved-expl@ %a@])" (Util.pp_list Lit.pp)
          self.lits
      else (
        let { lits; same_value; pr = _ } = self in
        Fmt.fprintf out "(@[resolved-expl@ (@[%a@])@ :same-val (@[%a@])@])"
          (Util.pp_list Lit.pp) lits
          (Util.pp_list @@ Fmt.Dump.pair E_node.pp E_node.pp)
          same_value
      )
  end

  type propagation_reason = unit -> lit list * step_id

  type action =
    | Act_merge of E_node.t * E_node.t * Expl.t
    | Act_propagate of { lit: lit; reason: propagation_reason }

  type conflict =
    | Conflict of lit list * step_id
        (** [raise_conflict (c,pr)] declares that [c] is a tautology of
          the theory of congruence.
          @param pr the proof of [c] being a tautology *)
    | Conflict_expl of Expl.t

  type actions_or_confl = (action list, conflict) result

  (** A signature is a shallow term shape where immediate subterms
      are representative *)
  module Signature = struct
    type t = signature

    let equal (s1 : t) s2 : bool =
      match s1, s2 with
      | Bool b1, Bool b2 -> b1 = b2
      | App_fun (f1, []), App_fun (f2, []) -> Fun.equal f1 f2
      | App_fun (f1, l1), App_fun (f2, l2) ->
        Fun.equal f1 f2 && CCList.equal E_node.equal l1 l2
      | App_ho (f1, a1), App_ho (f2, a2) ->
        E_node.equal f1 f2 && E_node.equal a1 a2
      | Not a, Not b -> E_node.equal a b
      | If (a1, b1, c1), If (a2, b2, c2) ->
        E_node.equal a1 a2 && E_node.equal b1 b2 && E_node.equal c1 c2
      | Eq (a1, b1), Eq (a2, b2) -> E_node.equal a1 a2 && E_node.equal b1 b2
      | Opaque u1, Opaque u2 -> E_node.equal u1 u2
      | Bool _, _
      | App_fun _, _
      | App_ho _, _
      | If _, _
      | Eq _, _
      | Opaque _, _
      | Not _, _ ->
        false

    let hash (s : t) : int =
      let module H = CCHash in
      match s with
      | Bool b -> H.combine2 10 (H.bool b)
      | App_fun (f, l) -> H.combine3 20 (Fun.hash f) (H.list E_node.hash l)
      | App_ho (f, a) -> H.combine3 30 (E_node.hash f) (E_node.hash a)
      | Eq (a, b) -> H.combine3 40 (E_node.hash a) (E_node.hash b)
      | Opaque u -> H.combine2 50 (E_node.hash u)
      | If (a, b, c) ->
        H.combine4 60 (E_node.hash a) (E_node.hash b) (E_node.hash c)
      | Not u -> H.combine2 70 (E_node.hash u)

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) ->
        Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list E_node.pp) l
      | App_ho (f, a) -> Fmt.fprintf out "(@[%a@ %a@])" E_node.pp f E_node.pp a
      | Opaque t -> E_node.pp out t
      | Not u -> Fmt.fprintf out "(@[not@ %a@])" E_node.pp u
      | Eq (a, b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" E_node.pp a E_node.pp b
      | If (a, b, c) ->
        Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" E_node.pp a E_node.pp b
          E_node.pp c
  end

  module Sig_tbl = CCHashtbl.Make (Signature)
  module T_tbl = CCHashtbl.Make (Term)
  module T_b_tbl = Backtrackable_tbl.Make (Term)

  type combine_task =
    | CT_merge of e_node * e_node * explanation
    | CT_set_val of e_node * value
    | CT_act of action

  type t = {
    tst: term_store;
    proof: proof_trace;
    tbl: e_node T_tbl.t; (* internalization [term -> e_node] *)
    signatures_tbl: e_node Sig_tbl.t;
    (* map a signature to the corresponding e_node in some equivalence class.
       A signature is a [term_cell] in which every immediate subterm
       that participates in the congruence/evaluation relation
       is normalized (i.e. is its own representative).
       The critical property is that all members of an equivalence class
       that have the same "shape" (including head symbol)
       have the same signature *)
    pending: e_node Vec.t;
    combine: combine_task Vec.t;
    t_to_val: (e_node * value) T_b_tbl.t;
    (* TODO: remove this, make it a plugin/EGG instead *)
    (* [repr -> (t,val)] where [repr = t] and [t := val] in the model *)
    val_to_t: e_node T_b_tbl.t; (* [val -> t] where [t := val] in the model *)
    undo: (unit -> unit) Backtrack_stack.t;
    bitgen: Bits.bitfield_gen;
    field_marked_explain: Bits.field;
    (* used to mark traversed nodes when looking for a common ancestor *)
    true_: e_node lazy_t;
    false_: e_node lazy_t;
    mutable model_mode: bool;
    mutable in_loop: bool; (* currently being modified? *)
    res_acts: action Vec.t; (* to return *)
    on_pre_merge:
      (t * E_node.t * E_node.t * Expl.t, actions_or_confl) Event.Emitter.t;
    on_post_merge: (t * E_node.t * E_node.t, action list) Event.Emitter.t;
    on_new_term: (t * E_node.t * term, action list) Event.Emitter.t;
    on_conflict: (ev_on_conflict, unit) Event.Emitter.t;
    on_propagate: (t * lit * propagation_reason, action list) Event.Emitter.t;
    on_is_subterm: (t * E_node.t * term, action list) Event.Emitter.t;
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

  and ev_on_conflict = { cc: t; th: bool; c: lit list }

  let[@inline] size_ (r : repr) = r.n_size
  let[@inline] n_true self = Lazy.force self.true_
  let[@inline] n_false self = Lazy.force self.false_

  let n_bool self b =
    if b then
      n_true self
    else
      n_false self

  let[@inline] term_store self = self.tst
  let[@inline] proof self = self.proof

  let allocate_bitfield self ~descr =
    Log.debugf 5 (fun k -> k "(@[cc.allocate-bit-field@ :descr %s@])" descr);
    Bits.mk_field self.bitgen

  let[@inline] on_backtrack self f : unit =
    Backtrack_stack.push_if_nonzero_level self.undo f

  let[@inline] get_bitfield _cc field n = E_node.get_field field n

  let set_bitfield self field b n =
    let old = E_node.get_field field n in
    if old <> b then (
      on_backtrack self (fun () -> E_node.set_field field old n);
      E_node.set_field field b n
    )

  (* check if [t] is in the congruence closure.
     Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
  let[@inline] mem (self : t) (t : term) : bool = T_tbl.mem self.tbl t

  module Debug_ = struct
    (* print full state *)
    let pp out (self : t) : unit =
      let pp_next out n = Fmt.fprintf out "@ :next %a" E_node.pp n.n_next in
      let pp_root out n =
        if E_node.is_root n then
          Fmt.string out " :is-root"
        else
          Fmt.fprintf out "@ :root %a" E_node.pp n.n_root
      in
      let pp_expl out n =
        match n.n_expl with
        | FL_none -> ()
        | FL_some e ->
          Fmt.fprintf out " (@[:forest %a :expl %a@])" E_node.pp e.next Expl.pp
            e.expl
      in
      let pp_n out n =
        Fmt.fprintf out "(@[%a%a%a%a@])" Term.pp n.n_term pp_root n pp_next n
          pp_expl n
      and pp_sig_e out (s, n) =
        Fmt.fprintf out "(@[<1>%a@ ~~> %a%a@])" Signature.pp s E_node.pp n
          pp_root n
      in
      Fmt.fprintf out
        "(@[@{<yellow>cc.state@}@ (@[<hv>:nodes@ %a@])@ (@[<hv>:sig-tbl@ \
         %a@])@])"
        (Util.pp_iter ~sep:" " pp_n)
        (T_tbl.values self.tbl)
        (Util.pp_iter ~sep:" " pp_sig_e)
        (Sig_tbl.to_iter self.signatures_tbl)
  end

  (* compute up-to-date signature *)
  let update_sig (s : signature) : Signature.t =
    View.map_view s ~f_f:(fun x -> x) ~f_t:find_ ~f_ts:(List.map find_)

  (* find whether the given (parent) term corresponds to some signature
     in [signatures_] *)
  let[@inline] find_signature cc (s : signature) : repr option =
    Sig_tbl.get cc.signatures_tbl s

  (* add to signature table. Assume it's not present already *)
  let add_signature self (s : signature) (n : e_node) : unit =
    assert (not @@ Sig_tbl.mem self.signatures_tbl s);
    Log.debugf 50 (fun k ->
        k "(@[cc.add-sig@ %a@ ~~> %a@])" Signature.pp s E_node.pp n);
    on_backtrack self (fun () -> Sig_tbl.remove self.signatures_tbl s);
    Sig_tbl.add self.signatures_tbl s n

  let push_pending self t : unit =
    Log.debugf 50 (fun k -> k "(@[<hv1>cc.push-pending@ %a@])" E_node.pp t);
    Vec.push self.pending t

  let push_action self (a : action) : unit = Vec.push self.combine (CT_act a)

  let push_action_l self (l : action list) : unit =
    List.iter (push_action self) l

  let merge_classes self t u e : unit =
    if t != u && not (same_class t u) then (
      Log.debugf 50 (fun k ->
          k "(@[<hv1>cc.push-combine@ %a ~@ %a@ :expl %a@])" E_node.pp t
            E_node.pp u Expl.pp e);
      Vec.push self.combine @@ CT_merge (t, u, e)
    )

  (* re-root the explanation tree of the equivalence class of [n]
     so that it points to [n].
     postcondition: [n.n_expl = None] *)
  let[@unroll 2] rec reroot_expl (self : t) (n : e_node) : unit =
    match n.n_expl with
    | FL_none -> () (* already root *)
    | FL_some { next = u; expl = e_n_u } ->
      (* reroot to [u], then invert link between [u] and [n] *)
      reroot_expl self u;
      u.n_expl <- FL_some { next = n; expl = e_n_u };
      n.n_expl <- FL_none

  exception E_confl of conflict

  let raise_conflict_ (cc : t) ~th (e : lit list) (p : step_id) : _ =
    Profile.instant "cc.conflict";
    (* clear tasks queue *)
    Vec.clear cc.pending;
    Vec.clear cc.combine;
    Event.emit cc.on_conflict { cc; th; c = e };
    Stat.incr cc.count_conflict;
    raise (E_confl (Conflict (e, p)))

  let[@inline] all_classes self : repr Iter.t =
    T_tbl.values self.tbl |> Iter.filter E_node.is_root

  (* find the closest common ancestor of [a] and [b] in the proof forest.

     Precond:
     - [a] and [b] are in the same class
     - no e_node has the flag [field_marked_explain] on
     Invariants:
     - if [n] is marked, then all the predecessors of [n]
       from [a] or [b] are marked too.
  *)
  let find_common_ancestor self (a : e_node) (b : e_node) : e_node =
    (* catch up to the other e_node *)
    let rec find1 a =
      if E_node.get_field self.field_marked_explain a then
        a
      else (
        match a.n_expl with
        | FL_none -> assert false
        | FL_some r -> find1 r.next
      )
    in
    let rec find2 a b =
      if E_node.equal a b then
        a
      else if E_node.get_field self.field_marked_explain a then
        a
      else if E_node.get_field self.field_marked_explain b then
        b
      else (
        E_node.set_field self.field_marked_explain true a;
        E_node.set_field self.field_marked_explain true b;
        match a.n_expl, b.n_expl with
        | FL_some r1, FL_some r2 -> find2 r1.next r2.next
        | FL_some r, FL_none -> find1 r.next
        | FL_none, FL_some r -> find1 r.next
        | FL_none, FL_none -> assert false
        (* no common ancestor *)
      )
    in

    (* cleanup tags on nodes traversed in [find2] *)
    let rec cleanup_ n =
      if E_node.get_field self.field_marked_explain n then (
        E_node.set_field self.field_marked_explain false n;
        match n.n_expl with
        | FL_none -> ()
        | FL_some { next; _ } -> cleanup_ next
      )
    in
    let n = find2 a b in
    cleanup_ a;
    cleanup_ b;
    n

  module Expl_state = struct
    type t = {
      mutable lits: Lit.t list;
      mutable same_val: (E_node.t * E_node.t) list;
      mutable th_lemmas: (Lit.t * (Lit.t * Lit.t list) list * step_id) list;
    }

    let create () : t = { lits = []; same_val = []; th_lemmas = [] }
    let[@inline] copy self : t = { self with lits = self.lits }
    let[@inline] add_lit (self : t) lit = self.lits <- lit :: self.lits

    let[@inline] add_th (self : t) lit hyps pr : unit =
      self.th_lemmas <- (lit, hyps, pr) :: self.th_lemmas

    let[@inline] add_same_val (self : t) n1 n2 : unit =
      self.same_val <- (n1, n2) :: self.same_val

    (** Does this explanation contain at least one merge caused by
        "same value"? *)
    let[@inline] is_semantic (self : t) : bool = self.same_val <> []

    let merge self other =
      let { lits = o_lits; th_lemmas = o_lemmas; same_val = o_same_val } =
        other
      in
      self.lits <- List.rev_append o_lits self.lits;
      self.th_lemmas <- List.rev_append o_lemmas self.th_lemmas;
      self.same_val <- List.rev_append o_same_val self.same_val;
      ()

    (* proof of [\/_i ¬lits[i]] *)
    let proof_of_th_lemmas (self : t) (proof : proof_trace) : step_id =
      let p_lits1 = Iter.of_list self.lits |> Iter.map Lit.neg in
      let p_lits2 =
        Iter.of_list self.th_lemmas
        |> Iter.map (fun (lit_t_u, _, _) -> Lit.neg lit_t_u)
      in
      let p_cc =
        P.add_step proof @@ Rules_.lemma_cc (Iter.append p_lits1 p_lits2)
      in
      let resolve_with_th_proof pr (lit_t_u, sub_proofs, pr_th) =
        (* pr_th: [sub_proofs |- t=u].
              now resolve away [sub_proofs] to get literals that were
              asserted in the congruence closure *)
        let pr_th =
          List.fold_left
            (fun pr_th (lit_i, hyps_i) ->
              (* [hyps_i |- lit_i] *)
              let lemma_i =
                P.add_step proof
                @@ Rules_.lemma_cc
                     Iter.(cons lit_i (of_list hyps_i |> map Lit.neg))
              in
              (* resolve [lit_i] away. *)
              P.add_step proof
              @@ Rules_.proof_res ~pivot:(Lit.term lit_i) lemma_i pr_th)
            pr_th sub_proofs
        in
        P.add_step proof @@ Rules_.proof_res ~pivot:(Lit.term lit_t_u) pr_th pr
      in
      (* resolve with theory proofs responsible for some merges, if any. *)
      List.fold_left resolve_with_th_proof p_cc self.th_lemmas

    let to_resolved_expl (self : t) : Resolved_expl.t =
      (* FIXME: package the th lemmas too *)
      let { lits; same_val; th_lemmas = _ } = self in
      let s2 = copy self in
      let pr proof = proof_of_th_lemmas s2 proof in
      { Resolved_expl.lits; same_value = same_val; pr }
  end

  (* decompose explanation [e] into a list of literals added to [acc] *)
  let rec explain_decompose_expl self (st : Expl_state.t) (e : explanation) :
      unit =
    Log.debugf 5 (fun k -> k "(@[cc.decompose_expl@ %a@])" Expl.pp e);
    match e with
    | E_trivial -> ()
    | E_congruence (n1, n2) ->
      (match n1.n_sig0, n2.n_sig0 with
      | Some (App_fun (f1, a1)), Some (App_fun (f2, a2)) ->
        assert (Fun.equal f1 f2);
        assert (List.length a1 = List.length a2);
        List.iter2 (explain_equal_rec_ self st) a1 a2
      | Some (App_ho (f1, a1)), Some (App_ho (f2, a2)) ->
        explain_equal_rec_ self st f1 f2;
        explain_equal_rec_ self st a1 a2
      | Some (If (a1, b1, c1)), Some (If (a2, b2, c2)) ->
        explain_equal_rec_ self st a1 a2;
        explain_equal_rec_ self st b1 b2;
        explain_equal_rec_ self st c1 c2
      | _ -> assert false)
    | E_lit lit -> Expl_state.add_lit st lit
    | E_same_val (n1, n2) -> Expl_state.add_same_val st n1 n2
    | E_theory (t, u, expl_sets, pr) ->
      let sub_proofs =
        List.map
          (fun (t_i, u_i, expls_i) ->
            let lit_i = A.mk_lit_eq self.tst t_i u_i in
            (* use a separate call to [explain_expls] for each set *)
            let sub = explain_expls self expls_i in
            Expl_state.merge st sub;
            lit_i, sub.lits)
          expl_sets
      in
      let lit_t_u = A.mk_lit_eq self.tst t u in
      Expl_state.add_th st lit_t_u sub_proofs pr
    | E_merge (a, b) -> explain_equal_rec_ self st a b
    | E_merge_t (a, b) ->
      (* find nodes for [a] and [b] on the fly *)
      (match T_tbl.find self.tbl a, T_tbl.find self.tbl b with
      | a, b -> explain_equal_rec_ self st a b
      | exception Not_found ->
        Error.errorf "expl: cannot find e_node(s) for %a, %a" Term.pp a Term.pp
          b)
    | E_and (a, b) ->
      explain_decompose_expl self st a;
      explain_decompose_expl self st b

  and explain_expls self (es : explanation list) : Expl_state.t =
    let st = Expl_state.create () in
    List.iter (explain_decompose_expl self st) es;
    st

  and explain_equal_rec_ (cc : t) (st : Expl_state.t) (a : e_node) (b : e_node)
      : unit =
    Log.debugf 5 (fun k ->
        k "(@[cc.explain_loop.at@ %a@ =?= %a@])" E_node.pp a E_node.pp b);
    assert (E_node.equal (find_ a) (find_ b));
    let ancestor = find_common_ancestor cc a b in
    explain_along_path cc st a ancestor;
    explain_along_path cc st b ancestor

  (* explain why [a = parent_a], where [a -> ... -> target] in the
     proof forest *)
  and explain_along_path self (st : Expl_state.t) (a : e_node) (target : e_node)
      : unit =
    let rec aux n =
      if n == target then
        ()
      else (
        match n.n_expl with
        | FL_none -> assert false
        | FL_some { next = next_n; expl } ->
          explain_decompose_expl self st expl;
          (* now prove [next_n = target] *)
          aux next_n
      )
    in
    aux a

  (* add a term *)
  let[@inline] rec add_term_rec_ self t : e_node =
    match T_tbl.find self.tbl t with
    | n -> n
    | exception Not_found -> add_new_term_ self t

  (* add [t] when not present already *)
  and add_new_term_ self (t : term) : e_node =
    assert (not @@ mem self t);
    Log.debugf 15 (fun k -> k "(@[cc.add-term@ %a@])" Term.pp t);
    let n = E_node.make t in
    (* register sub-terms, add [t] to their parent list, and return the
       corresponding initial signature *)
    let sig0 = compute_sig0 self n in
    n.n_sig0 <- sig0;
    (* remove term when we backtrack *)
    on_backtrack self (fun () ->
        Log.debugf 30 (fun k -> k "(@[cc.remove-term@ %a@])" Term.pp t);
        T_tbl.remove self.tbl t);
    (* add term to the table *)
    T_tbl.add self.tbl t n;
    if Option.is_some sig0 then
      (* [n] might be merged with other equiv classes *)
      push_pending self n;
    if not self.model_mode then
      Event.emit_iter self.on_new_term (self, n, t) ~f:(push_action_l self);
    n

  (* compute the initial signature of the given e_node *)
  and compute_sig0 (self : t) (n : e_node) : Signature.t option =
    (* add sub-term to [cc], and register [n] to its parents.
       Note that we return the exact sub-term, to get proper
       explanations, but we add to the sub-term's root's parent list. *)
    let deref_sub (u : term) : e_node =
      let sub = add_term_rec_ self u in
      (* add [n] to [sub.root]'s parent list *)
      (let sub_r = find_ sub in
       let old_parents = sub_r.n_parents in
       if Bag.is_empty old_parents && not self.model_mode then
         (* first time it has parents: tell watchers that this is a subterm *)
         Event.emit_iter self.on_is_subterm (self, sub, u)
           ~f:(push_action_l self);
       on_backtrack self (fun () -> sub_r.n_parents <- old_parents);
       sub_r.n_parents <- Bag.cons n sub_r.n_parents);
      sub
    in
    let[@inline] return x = Some x in
    match A.view_as_cc n.n_term with
    | Bool _ | Opaque _ -> None
    | Eq (a, b) ->
      let a = deref_sub a in
      let b = deref_sub b in
      return @@ Eq (a, b)
    | Not u -> return @@ Not (deref_sub u)
    | App_fun (f, args) ->
      let args = args |> Iter.map deref_sub |> Iter.to_list in
      if args <> [] then
        return @@ App_fun (f, args)
      else
        None
    | App_ho (f, a) ->
      let f = deref_sub f in
      let a = deref_sub a in
      return @@ App_ho (f, a)
    | If (a, b, c) -> return @@ If (deref_sub a, deref_sub b, deref_sub c)

  let[@inline] add_term self t : e_node = add_term_rec_ self t
  let mem_term = mem

  let set_as_lit self (n : e_node) (lit : lit) : unit =
    match n.n_as_lit with
    | Some _ -> ()
    | None ->
      Log.debugf 15 (fun k ->
          k "(@[cc.set-as-lit@ %a@ %a@])" E_node.pp n Lit.pp lit);
      on_backtrack self (fun () -> n.n_as_lit <- None);
      n.n_as_lit <- Some lit

  (* is [n] true or false? *)
  let n_is_bool_value (self : t) n : bool =
    E_node.equal n (n_true self) || E_node.equal n (n_false self)

  (* gather a pair [lits, pr], where [lits] is the set of
     asserted literals needed in the explanation (which is useful for
     the SAT solver), and [pr] is a proof, including sub-proofs for theory
     merges. *)
  let lits_and_proof_of_expl (self : t) (st : Expl_state.t) :
      Lit.t list * step_id =
    let { Expl_state.lits; th_lemmas = _; same_val } = st in
    assert (same_val = []);
    let pr = Expl_state.proof_of_th_lemmas st self.proof in
    lits, pr

  (* main CC algo: add terms from [pending] to the signature table,
     check for collisions *)
  let rec update_tasks (self : t) : unit =
    while not (Vec.is_empty self.pending && Vec.is_empty self.combine) do
      while not @@ Vec.is_empty self.pending do
        task_pending_ self (Vec.pop_exn self.pending)
      done;
      while not @@ Vec.is_empty self.combine do
        task_combine_ self (Vec.pop_exn self.combine)
      done
    done

  and task_pending_ self (n : e_node) : unit =
    (* check if some parent collided *)
    match n.n_sig0 with
    | None -> () (* no-op *)
    | Some (Eq (a, b)) ->
      (* if [a=b] is now true, merge [(a=b)] and [true] *)
      if same_class a b then (
        let expl = Expl.mk_merge a b in
        Log.debugf 5 (fun k ->
            k "(@[cc.pending.eq@ %a@ :r1 %a@ :r2 %a@])" E_node.pp n E_node.pp a
              E_node.pp b);
        merge_classes self n (n_true self) expl
      )
    | Some (Not u) ->
      (* [u = bool ==> not u = not bool] *)
      let r_u = find_ u in
      if E_node.equal r_u (n_true self) then (
        let expl = Expl.mk_merge u (n_true self) in
        merge_classes self n (n_false self) expl
      ) else if E_node.equal r_u (n_false self) then (
        let expl = Expl.mk_merge u (n_false self) in
        merge_classes self n (n_true self) expl
      )
    | Some s0 ->
      (* update the signature by using [find] on each sub-e_node *)
      let s = update_sig s0 in
      (match find_signature self s with
      | None ->
        (* add to the signature table [sig(n) --> n] *)
        add_signature self s n
      | Some u when E_node.equal n u -> ()
      | Some u ->
        (* [t1] and [t2] must be applications of the same symbol to
             arguments that are pairwise equal *)
        assert (n != u);
        let expl = Expl.mk_congruence n u in
        merge_classes self n u expl)

  and task_combine_ self = function
    | CT_merge (a, b, e_ab) -> task_merge_ self a b e_ab
    | CT_set_val (n, v) -> task_set_val_ self n v
    | CT_act (Act_merge (t, u, e)) -> task_merge_ self t u e
    | CT_act (Act_propagate _ as a) ->
      (* will return this propagation to the caller *)
      Vec.push self.res_acts a

  and task_set_val_ self n v =
    let repr_n = find_ n in
    (* - if repr(n) has value [v], do nothing
       - else if repr(n) has value [v'], semantic conflict
       - else add [repr(n) -> (n,v)] to cc.t_to_val *)
    (match T_b_tbl.get self.t_to_val repr_n.n_term with
    | Some (n', v') when not (Term.equal v v') ->
      (* semantic conflict *)
      let expl = [ Expl.mk_merge n n' ] in
      let expl_st = explain_expls self expl in
      let lits = expl_st.lits in
      let tuples =
        List.rev_map (fun (t, u) -> true, t.n_term, u.n_term) expl_st.same_val
      in
      let tuples = (false, n.n_term, n'.n_term) :: tuples in
      Log.debugf 5 (fun k ->
          k
            "(@[cc.semantic-conflict.set-val@ (@[set-val %a@ := %a@])@ \
             (@[existing-val %a@ := %a@])@])"
            E_node.pp n Term.pp v E_node.pp n' Term.pp v');

      Stat.incr self.count_semantic_conflict;
      (* FIXME
         raise (E_confl(Conflict lits))
         let (module A) = acts in
         A.raise_semantic_conflict lits tuples
      *)
      assert false
    | Some _ -> ()
    | None -> T_b_tbl.add self.t_to_val repr_n.n_term (n, v));
    (* now for the reverse map, look in self.val_to_t for [v].
       - if present, push a merge command with Expl.mk_same_value
       - if not, add [v -> n] *)
    match T_b_tbl.get self.val_to_t v with
    | None -> T_b_tbl.add self.val_to_t v n
    | Some n' when not (same_class n n') ->
      merge_classes self n n' (Expl.mk_same_value n n')
    | Some _ -> ()

  (* main CC algo: merge equivalence classes in [st.combine].
     @raise Exn_unsat if merge fails *)
  and task_merge_ self a b e_ab : unit =
    let ra = find_ a in
    let rb = find_ b in
    if not @@ E_node.equal ra rb then (
      assert (E_node.is_root ra);
      assert (E_node.is_root rb);
      Stat.incr self.count_merge;
      (* check we're not merging [true] and [false] *)
      if
        (E_node.equal ra (n_true self) && E_node.equal rb (n_false self))
        || (E_node.equal rb (n_true self) && E_node.equal ra (n_false self))
      then (
        Log.debugf 5 (fun k ->
            k
              "(@[<hv>cc.merge.true_false_conflict@ @[:r1 %a@ :t1 %a@]@ @[:r2 \
               %a@ :t2 %a@]@ :e_ab %a@])"
              E_node.pp ra E_node.pp a E_node.pp rb E_node.pp b Expl.pp e_ab);
        let th = ref false in
        (* TODO:
           C1: P.true_neq_false
           C2: lemma [lits |- true=false]  (and resolve on theory proofs)
           C3: r1 C1 C2
        *)
        let expl_st = Expl_state.create () in
        explain_decompose_expl self expl_st e_ab;
        explain_equal_rec_ self expl_st a ra;
        explain_equal_rec_ self expl_st b rb;

        if Expl_state.is_semantic expl_st then (
          (* conflict involving some semantic values *)
          let lits = expl_st.lits in
          let same_val =
            expl_st.same_val
            |> List.rev_map (fun (t, u) -> true, E_node.term t, E_node.term u)
          in
          assert (same_val <> []);
          Stat.incr self.count_semantic_conflict;
          (* FIXME
             let (module A) = acts in
             A.raise_semantic_conflict lits same_val
          *)
          assert false
        ) else (
          (* regular conflict *)
          let lits, pr = lits_and_proof_of_expl self expl_st in
          raise_conflict_ self ~th:!th (List.rev_map Lit.neg lits) pr
        )
      );
      (* We will merge [r_from] into [r_into].
         we try to ensure that [size ra <= size rb] in general, but always
         keep values as representative *)
      let r_from, r_into =
        if n_is_bool_value self ra then
          rb, ra
        else if n_is_bool_value self rb then
          ra, rb
        else if size_ ra > size_ rb then
          rb, ra
        else
          ra, rb
      in
      (* when merging terms with [true] or [false], possibly propagate them to SAT *)
      let merge_bool r1 t1 r2 t2 =
        if E_node.equal r1 (n_true self) then
          propagate_bools self r2 t2 r1 t1 e_ab true
        else if E_node.equal r1 (n_false self) then
          propagate_bools self r2 t2 r1 t1 e_ab false
      in

      if not self.model_mode then (
        merge_bool ra a rb b;
        merge_bool rb b ra a
      );

      (* perform [union r_from r_into] *)
      Log.debugf 15 (fun k ->
          k "(@[cc.merge@ :from %a@ :into %a@])" E_node.pp r_from E_node.pp
            r_into);

      (* call [on_pre_merge] functions, and merge theory data items *)
      if not self.model_mode then (
        (* explanation is [a=ra & e_ab & b=rb] *)
        let expl =
          Expl.mk_list [ e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb ]
        in
        Event.emit_iter self.on_pre_merge (self, r_into, r_from, expl)
          ~f:(function
          | Ok l -> push_action_l self l
          | Error c -> raise (E_confl c))
      );

      (* TODO: merge plugin data here, _after_ the pre-merge hooks are called,
         so they have a chance of observing pre-merge plugin data *)
      ((* parents might have a different signature, check for collisions *)
       E_node.iter_parents r_from (fun parent -> push_pending self parent);
       (* for each e_node in [r_from]'s class, make it point to [r_into] *)
       E_node.iter_class r_from (fun u ->
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
       on_backtrack self (fun () ->
           Log.debugf 30 (fun k ->
               k "(@[cc.undo_merge@ :from %a@ :into %a@])" E_node.pp r_from
                 E_node.pp r_into);
           r_into.n_bits <- r_into_old_bits;
           r_into.n_next <- r_into_old_next;
           r_from.n_next <- r_from_old_next;
           r_into.n_parents <- r_into_old_parents;
           (* NOTE: this must come after the restoration of [next] pointers,
              otherwise we'd iterate on too big a class *)
           E_node.iter_class_ r_from (fun u -> u.n_root <- r_from);
           r_into.n_size <- r_into.n_size - r_from.n_size));

      (* check for semantic values, update the one of [r_into]
         if [r_from] has a value *)
      (match T_b_tbl.get self.t_to_val r_from.n_term with
      | None -> ()
      | Some (n_from, v_from) ->
        (match T_b_tbl.get self.t_to_val r_into.n_term with
        | None -> T_b_tbl.add self.t_to_val r_into.n_term (n_from, v_from)
        | Some (n_into, v_into) when not (Term.equal v_from v_into) ->
          (* semantic conflict, including [n_from != n_into] in model *)
          let expl =
            [ e_ab; Expl.mk_merge r_from n_from; Expl.mk_merge r_into n_into ]
          in
          let expl_st = explain_expls self expl in
          let lits = expl_st.lits in
          let tuples =
            List.rev_map
              (fun (t, u) -> true, t.n_term, u.n_term)
              expl_st.same_val
          in
          let tuples = (false, n_from.n_term, n_into.n_term) :: tuples in

          Log.debugf 5 (fun k ->
              k
                "(@[cc.semantic-conflict.post-merge@ (@[n-from %a@ := %a@])@ \
                 (@[n-into %a@ := %a@])@])"
                E_node.pp n_from Term.pp v_from E_node.pp n_into Term.pp v_into);

          Stat.incr self.count_semantic_conflict;
          (* FIXME
             let (module A) = acts in
             A.raise_semantic_conflict lits tuples
          *)
          assert false
        | Some _ -> ()));

      (* update explanations (a -> b), arbitrarily.
         Note that here we merge the classes by adding a bridge between [a]
         and [b], not their roots. *)
      reroot_expl self a;
      assert (a.n_expl = FL_none);
      (* on backtracking, link may be inverted, but we delete the one
         that bridges between [a] and [b] *)
      on_backtrack self (fun () ->
          match a.n_expl, b.n_expl with
          | FL_some e, _ when E_node.equal e.next b -> a.n_expl <- FL_none
          | _, FL_some e when E_node.equal e.next a -> b.n_expl <- FL_none
          | _ -> assert false);
      a.n_expl <- FL_some { next = b; expl = e_ab };
      (* call [on_post_merge] *)
      if not self.model_mode then
        Event.emit_iter self.on_post_merge (self, r_into, r_from)
          ~f:(push_action_l self)
    )

  (* we are merging [r1] with [r2==Bool(sign)], so propagate each term [u1]
     in the equiv class of [r1] that is a known literal back to the SAT solver
     and which is not the one initially merged.
     We can explain the propagation with [u1 = t1 =e= t2 = r2==bool] *)
  and propagate_bools self r1 t1 r2 t2 (e_12 : explanation) sign : unit =
    (* explanation for [t1 =e= t2 = r2] *)
    let half_expl_and_pr =
      lazy
        (let st = Expl_state.create () in
         explain_decompose_expl self st e_12;
         explain_equal_rec_ self st r2 t2;
         st)
    in
    (* TODO: flag per class, `or`-ed on merge, to indicate if the class
       contains at least one lit *)
    E_node.iter_class r1 (fun u1 ->
        (* propagate if:
           - [u1] is a proper literal
           - [t2 != r2], because that can only happen
             after an explicit merge (no way to obtain that by propagation)
        *)
        match E_node.as_lit u1 with
        | Some lit when not (E_node.equal r2 t2) ->
          let lit =
            if sign then
              lit
            else
              Lit.neg lit
          in
          (* apply sign *)
          Log.debugf 5 (fun k -> k "(@[cc.bool_propagate@ %a@])" Lit.pp lit);
          (* complete explanation with the [u1=t1] chunk *)
          let (lazy st) = half_expl_and_pr in
          let st = Expl_state.copy st in
          (* do not modify shared st *)
          explain_equal_rec_ self st u1 t1;

          (* propagate only if this doesn't depend on some semantic values *)
          if not (Expl_state.is_semantic st) then (
            let reason () =
              (* true literals explaining why t1=t2 *)
              let guard = st.lits in
              (* get a proof of [guard /\ ¬lit] being absurd, to propagate [lit] *)
              Expl_state.add_lit st (Lit.neg lit);
              let _, pr = lits_and_proof_of_expl self st in
              guard, pr
            in
            push_action self (Act_propagate { lit; reason });
            Event.emit_iter self.on_propagate (self, lit, reason)
              ~f:(push_action_l self);
            Stat.incr self.count_props
          )
        | _ -> ())

  let add_iter self it : unit = it (fun t -> ignore @@ add_term_rec_ self t)

  let push_level (self : t) : unit =
    assert (not self.in_loop);
    Backtrack_stack.push_level self.undo;
    T_b_tbl.push_level self.t_to_val;
    T_b_tbl.push_level self.val_to_t

  let pop_levels (self : t) n : unit =
    assert (not self.in_loop);
    Vec.clear self.pending;
    Vec.clear self.combine;
    Log.debugf 15 (fun k ->
        k "(@[cc.pop-levels %d@ :n-lvls %d@])" n
          (Backtrack_stack.n_levels self.undo));
    Backtrack_stack.pop_levels self.undo n ~f:(fun f -> f ());
    T_b_tbl.pop_levels self.t_to_val n;
    T_b_tbl.pop_levels self.val_to_t n;
    ()

  (* FIXME: remove *)
  (* run [f] in a local congruence closure level *)
  let with_model_mode self f =
    assert (not self.model_mode);
    self.model_mode <- true;
    push_level self;
    CCFun.protect f ~finally:(fun () ->
        pop_levels self 1;
        self.model_mode <- false)

  let get_model_for_each_class self : _ Iter.t =
    assert self.model_mode;
    all_classes self
    |> Iter.filter_map (fun repr ->
           match T_b_tbl.get self.t_to_val repr.n_term with
           | Some (_, v) -> Some (repr, E_node.iter_class repr, v)
           | None -> None)

  let assert_eq self t u expl : unit =
    assert (not self.in_loop);
    let t = add_term self t in
    let u = add_term self u in
    (* merge [a] and [b] *)
    merge_classes self t u expl

  (* assert that this boolean literal holds.
     if a lit is [= a b], merge [a] and [b];
     otherwise merge the atom with true/false *)
  let assert_lit self lit : unit =
    assert (not self.in_loop);
    let t = Lit.term lit in
    Log.debugf 15 (fun k -> k "(@[cc.assert-lit@ %a@])" Lit.pp lit);
    let sign = Lit.sign lit in
    match A.view_as_cc t with
    | Eq (a, b) when sign -> assert_eq self a b (Expl.mk_lit lit)
    | _ ->
      (* equate t and true/false *)
      let rhs = n_bool self sign in
      let n = add_term self t in
      (* TODO: ensure that this is O(1).
         basically, just have [n] point to true/false and thus acquire
         the corresponding value, so its superterms (like [ite]) can evaluate
         properly *)
      (* TODO: use oriented merge (force direction [n -> rhs]) *)
      merge_classes self n rhs (Expl.mk_lit lit)

  let[@inline] assert_lits self lits : unit =
    assert (not self.in_loop);
    Iter.iter (assert_lit self) lits

  (* FIXME: remove?
     (* raise a conflict *)
     let raise_conflict_from_expl self (acts : actions_or_confl) expl =
       Log.debugf 5 (fun k ->
           k "(@[cc.theory.raise-conflict@ :expl %a@])" Expl.pp expl);
       let st = Expl_state.create () in
       explain_decompose_expl self st expl;
       let lits, pr = lits_and_proof_of_expl self st in
       let c = List.rev_map Lit.neg lits in
       let th = st.th_lemmas <> [] in
       raise_conflict_ self ~th c pr
  *)

  let merge self n1 n2 expl =
    assert (not self.in_loop);
    Log.debugf 5 (fun k ->
        k "(@[cc.theory.merge@ :n1 %a@ :n2 %a@ :expl %a@])" E_node.pp n1
          E_node.pp n2 Expl.pp expl);
    assert (T.Ty.equal (T.Term.ty n1.n_term) (T.Term.ty n2.n_term));
    merge_classes self n1 n2 expl

  let merge_t self t1 t2 expl =
    merge self (add_term self t1) (add_term self t2) expl

  let set_model_value (self : t) (t : term) (v : value) : unit =
    assert (not self.in_loop);
    assert self.model_mode;
    (* only valid in model mode *)
    match T_tbl.find_opt self.tbl t with
    | None -> () (* ignore, th combination not needed *)
    | Some n -> Vec.push self.combine (CT_set_val (n, v))

  let explain_eq self n1 n2 : Resolved_expl.t =
    let st = Expl_state.create () in
    explain_equal_rec_ self st n1 n2;
    (* FIXME: also need to return the proof? *)
    Expl_state.to_resolved_expl st

  let[@inline] on_pre_merge self = Event.of_emitter self.on_pre_merge
  let[@inline] on_post_merge self = Event.of_emitter self.on_post_merge
  let[@inline] on_new_term self = Event.of_emitter self.on_new_term
  let[@inline] on_conflict self = Event.of_emitter self.on_conflict
  let[@inline] on_propagate self = Event.of_emitter self.on_propagate
  let[@inline] on_is_subterm self = Event.of_emitter self.on_is_subterm

  let create ?(stat = Stat.global) ?(size = `Big) (tst : term_store)
      (proof : proof_trace) : t =
    let size =
      match size with
      | `Small -> 128
      | `Big -> 2048
    in
    let bitgen = Bits.mk_gen () in
    let field_marked_explain = Bits.mk_field bitgen in
    let rec cc =
      {
        tst;
        proof;
        tbl = T_tbl.create size;
        signatures_tbl = Sig_tbl.create size;
        bitgen;
        t_to_val = T_b_tbl.create ~size:32 ();
        val_to_t = T_b_tbl.create ~size:32 ();
        model_mode = false;
        on_pre_merge = Event.Emitter.create ();
        on_post_merge = Event.Emitter.create ();
        on_new_term = Event.Emitter.create ();
        on_conflict = Event.Emitter.create ();
        on_propagate = Event.Emitter.create ();
        on_is_subterm = Event.Emitter.create ();
        pending = Vec.create ();
        combine = Vec.create ();
        undo = Backtrack_stack.create ();
        true_;
        false_;
        in_loop = false;
        res_acts = Vec.create ();
        field_marked_explain;
        count_conflict = Stat.mk_int stat "cc.conflicts";
        count_props = Stat.mk_int stat "cc.propagations";
        count_merge = Stat.mk_int stat "cc.merges";
        count_semantic_conflict = Stat.mk_int stat "cc.semantic-conflicts";
      }
    and true_ = lazy (add_term cc (Term.bool tst true))
    and false_ = lazy (add_term cc (Term.bool tst false)) in
    ignore (Lazy.force true_ : e_node);
    ignore (Lazy.force false_ : e_node);
    cc

  let[@inline] find_t self t : repr =
    let n = T_tbl.find self.tbl t in
    find_ n

  let pop_acts_ self =
    let rec loop acc =
      match Vec.pop self.res_acts with
      | None -> acc
      | Some x -> loop (x :: acc)
    in
    loop []

  let check self : actions_or_confl =
    Log.debug 5 "(cc.check)";
    self.in_loop <- true;
    let@ () = Stdlib.Fun.protect ~finally:(fun () -> self.in_loop <- false) in
    try
      update_tasks self;
      let l = pop_acts_ self in
      Ok l
    with E_confl c -> Error c

  let check_inv_enabled_ = true (* XXX NUDGE *)

  (* check some internal invariants *)
  let check_inv_ (self : t) : unit =
    if check_inv_enabled_ then (
      Log.debug 2 "(cc.check-invariants)";
      all_classes self
      |> Iter.flat_map E_node.iter_class
      |> Iter.iter (fun n ->
             match n.n_sig0 with
             | None -> ()
             | Some s ->
               let s' = update_sig s in
               let ok =
                 match find_signature self s' with
                 | None -> false
                 | Some r -> E_node.equal r n.n_root
               in
               if not ok then
                 Log.debugf 0 (fun k ->
                     k "(@[cc.check.fail@ :n %a@ :sig %a@ :actual-sig %a@])"
                       E_node.pp n Signature.pp s Signature.pp s'))
    )

  (* model: return all the classes *)
  let get_model (self : t) : repr Iter.t Iter.t =
    check_inv_ self;
    all_classes self |> Iter.map E_node.iter_class
end
