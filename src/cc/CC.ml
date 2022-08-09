open Types_

type view_as_cc = Term.t -> (Const.t, Term.t, Term.t list) CC_view.t

type e_node = E_node.t
(** A node of the congruence closure *)

type repr = E_node.t
(** Node that is currently a representative. *)

type explanation = Expl.t
type bitfield = Bits.field

(* non-recursive, inlinable function for [find] *)
let[@inline] find_ (n : e_node) : repr =
  let n2 = n.n_root in
  assert (E_node.is_root n2);
  n2

let[@inline] same_class (n1 : e_node) (n2 : e_node) : bool =
  E_node.equal (find_ n1) (find_ n2)

let[@inline] find _ n = find_ n

module Sig_tbl = CCHashtbl.Make (Signature)
module T_tbl = Term.Tbl

type propagation_reason = unit -> Lit.t list * Proof_term.step_id

module Handler_action = struct
  type t =
    | Act_merge of E_node.t * E_node.t * Expl.t
    | Act_propagate of Lit.t * propagation_reason

  type conflict = Conflict of Expl.t [@@unboxed]
  type or_conflict = (t list, conflict) result
end

module Result_action = struct
  type t = Act_propagate of { lit: Lit.t; reason: propagation_reason }
  type conflict = Conflict of Lit.t list * Proof_term.step_id
  type or_conflict = (t list, conflict) result
end

type combine_task =
  | CT_merge of e_node * e_node * explanation
  | CT_act of Handler_action.t

type t = {
  view_as_cc: view_as_cc;
  tst: Term.store;
  proof: Proof_trace.t;
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
  undo: (unit -> unit) Backtrack_stack.t;
  bitgen: Bits.bitfield_gen;
  field_marked_explain: Bits.field;
  (* used to mark traversed nodes when looking for a common ancestor *)
  true_: e_node lazy_t;
  false_: e_node lazy_t;
  mutable in_loop: bool; (* currently being modified? *)
  res_acts: Result_action.t Vec.t; (* to return *)
  on_pre_merge:
    ( t * E_node.t * E_node.t * Expl.t,
      Handler_action.or_conflict )
    Event.Emitter.t;
  on_pre_merge2:
    ( t * E_node.t * E_node.t * Expl.t,
      Handler_action.or_conflict )
    Event.Emitter.t;
  on_post_merge:
    (t * E_node.t * E_node.t, Handler_action.t list) Event.Emitter.t;
  on_new_term: (t * E_node.t * Term.t, Handler_action.t list) Event.Emitter.t;
  on_conflict: (ev_on_conflict, unit) Event.Emitter.t;
  on_propagate:
    (t * Lit.t * propagation_reason, Handler_action.t list) Event.Emitter.t;
  on_is_subterm: (t * E_node.t * Term.t, Handler_action.t list) Event.Emitter.t;
  count_conflict: int Stat.counter;
  count_props: int Stat.counter;
  count_merge: int Stat.counter;
}
(* TODO: an additional union-find to keep track, for each term,
   of the terms they are known to be equal to, according
   to the current explanation. That allows not to prove some equality
   several times.
   See "fast congruence closure and extensions", Nieuwenhuis&al, page 14 *)

and ev_on_conflict = { cc: t; th: bool; c: Lit.t list }

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

let allocate_bitfield self ~descr : bitfield =
  Log.debugf 5 (fun k -> k "(@[cc.allocate-bit-field@ :descr %s@])" descr);
  Bits.mk_field self.bitgen

let[@inline] on_backtrack self f : unit =
  Backtrack_stack.push_if_nonzero_level self.undo f

let[@inline] set_bitfield_ f b t = t.n_bits <- Bits.set f b t.n_bits
let[@inline] get_bitfield_ field n = Bits.get field n.n_bits
let[@inline] get_bitfield _cc field n = get_bitfield_ field n

let set_bitfield self field b n =
  let old = get_bitfield self field n in
  if old <> b then (
    on_backtrack self (fun () -> set_bitfield_ field old n);
    set_bitfield_ field b n
  )

(* check if [t] is in the congruence closure.
   Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
let[@inline] mem (self : t) (t : Term.t) : bool = T_tbl.mem self.tbl t

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
      Fmt.fprintf out "(@[%a%a%a%a@])" Term.pp_debug n.n_term pp_root n pp_next
        n pp_expl n
    and pp_sig_e out (s, n) =
      Fmt.fprintf out "(@[<1>%a@ ~~> %a%a@])" Signature.pp s E_node.pp n pp_root
        n
    in
    Fmt.fprintf out
      "(@[@{<yellow>cc.state@}@ (@[<hv>:nodes@ %a@])@ (@[<hv>:sig-tbl@ %a@])@])"
      (Util.pp_iter ~sep:" " pp_n)
      (T_tbl.values self.tbl)
      (Util.pp_iter ~sep:" " pp_sig_e)
      (Sig_tbl.to_iter self.signatures_tbl)
end

(* compute up-to-date signature *)
let update_sig (s : signature) : Signature.t =
  CC_view.map_view s ~f_f:(fun x -> x) ~f_t:find_ ~f_ts:(List.map find_)

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

let push_action self (a : Handler_action.t) : unit =
  Vec.push self.combine (CT_act a)

let push_action_l self (l : _ list) : unit = List.iter (push_action self) l

let merge_classes self t u e : unit =
  if t != u && not (same_class t u) then (
    Log.debugf 50 (fun k ->
        k "(@[<hv1>cc.push-combine@ %a ~@ %a@ :expl %a@])" E_node.pp t E_node.pp
          u Expl.pp e);
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

exception E_confl of Result_action.conflict

let raise_conflict_ (cc : t) ~th (e : Lit.t list) (p : Proof_term.step_id) : _ =
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
    if get_bitfield_ self.field_marked_explain a then
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
    else if get_bitfield_ self.field_marked_explain a then
      a
    else if get_bitfield_ self.field_marked_explain b then
      b
    else (
      set_bitfield_ self.field_marked_explain true a;
      set_bitfield_ self.field_marked_explain true b;
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
    if get_bitfield_ self.field_marked_explain n then (
      set_bitfield_ self.field_marked_explain false n;
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
    mutable th_lemmas:
      (Lit.t * (Lit.t * Lit.t list) list * Proof_term.step_id) list;
  }

  let create () : t = { lits = []; th_lemmas = [] }
  let[@inline] copy self : t = { self with lits = self.lits }
  let[@inline] add_lit (self : t) lit = self.lits <- lit :: self.lits

  let[@inline] add_th (self : t) lit hyps pr : unit =
    self.th_lemmas <- (lit, hyps, pr) :: self.th_lemmas

  let merge self other =
    let { lits = o_lits; th_lemmas = o_lemmas } = other in
    self.lits <- List.rev_append o_lits self.lits;
    self.th_lemmas <- List.rev_append o_lemmas self.th_lemmas;
    ()

  (* proof of [\/_i ¬lits[i]] *)
  let proof_of_th_lemmas (self : t) (proof : Proof_trace.t) : Proof_term.step_id
      =
    let p_lits1 = List.rev_map Lit.neg self.lits in
    let p_lits2 =
      self.th_lemmas |> List.rev_map (fun (lit_t_u, _, _) -> Lit.neg lit_t_u)
    in
    let p_cc =
      Proof_trace.add_step proof @@ fun () ->
      Proof_core.lemma_cc (List.rev_append p_lits1 p_lits2)
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
              Proof_trace.add_step proof @@ fun () ->
              Proof_core.lemma_cc (lit_i :: List.rev_map Lit.neg hyps_i)
            in
            (* resolve [lit_i] away. *)
            Proof_trace.add_step proof @@ fun () ->
            Proof_core.proof_res ~pivot:(Lit.term lit_i) lemma_i pr_th)
          pr_th sub_proofs
      in
      Proof_trace.add_step proof @@ fun () ->
      Proof_core.proof_res ~pivot:(Lit.term lit_t_u) pr_th pr
    in
    (* resolve with theory proofs responsible for some merges, if any. *)
    List.fold_left resolve_with_th_proof p_cc self.th_lemmas

  let to_resolved_expl (self : t) : Resolved_expl.t =
    (* FIXME: package the th lemmas too *)
    let { lits; th_lemmas = _ } = self in
    let s2 = copy self in
    let pr proof = proof_of_th_lemmas s2 proof in
    { Resolved_expl.lits; pr }
end

(* decompose explanation [e] into a list of literals added to [acc] *)
let rec explain_decompose_expl self (st : Expl_state.t) (e : explanation) : unit
    =
  Log.debugf 5 (fun k -> k "(@[cc.decompose_expl@ %a@])" Expl.pp e);
  match e with
  | E_trivial -> ()
  | E_congruence (n1, n2) ->
    (match n1.n_sig0, n2.n_sig0 with
    | Some (App_fun (f1, a1)), Some (App_fun (f2, a2)) ->
      assert (Const.equal f1 f2);
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
  | E_theory (t, u, expl_sets, pr) ->
    let sub_proofs =
      List.map
        (fun (t_i, u_i, expls_i) ->
          let lit_i = Lit.make_eq self.tst t_i u_i in
          (* use a separate call to [explain_expls] for each set *)
          let sub = explain_expls self expls_i in
          Expl_state.merge st sub;
          lit_i, sub.lits)
        expl_sets
    in
    let lit_t_u = Lit.make_eq self.tst t u in
    Expl_state.add_th st lit_t_u sub_proofs pr
  | E_merge (a, b) -> explain_equal_rec_ self st a b
  | E_merge_t (a, b) ->
    (* find nodes for [a] and [b] on the fly *)
    (match T_tbl.find self.tbl a, T_tbl.find self.tbl b with
    | a, b -> explain_equal_rec_ self st a b
    | exception Not_found ->
      Error.errorf "expl: cannot find e_node(s) for %a, %a" Term.pp_debug a
        Term.pp_debug b)
  | E_and (a, b) ->
    explain_decompose_expl self st a;
    explain_decompose_expl self st b

and explain_expls self (es : explanation list) : Expl_state.t =
  let st = Expl_state.create () in
  List.iter (explain_decompose_expl self st) es;
  st

and explain_equal_rec_ (cc : t) (st : Expl_state.t) (a : e_node) (b : e_node) :
    unit =
  Log.debugf 5 (fun k ->
      k "(@[cc.explain_loop.at@ %a@ =?= %a@])" E_node.pp a E_node.pp b);
  assert (E_node.equal (find_ a) (find_ b));
  let ancestor = find_common_ancestor cc a b in
  explain_along_path cc st a ancestor;
  explain_along_path cc st b ancestor

(* explain why [a = parent_a], where [a -> ... -> target] in the
   proof forest *)
and explain_along_path self (st : Expl_state.t) (a : e_node) (target : e_node) :
    unit =
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
and add_new_term_ self (t : Term.t) : e_node =
  assert (not @@ mem self t);
  Log.debugf 15 (fun k -> k "(@[cc.add-term@ %a@])" Term.pp_debug t);
  let n = E_node.Internal_.make t in
  (* register sub-terms, add [t] to their parent list, and return the
     corresponding initial signature *)
  let sig0 = compute_sig0 self n in
  n.n_sig0 <- sig0;
  (* remove term when we backtrack *)
  on_backtrack self (fun () ->
      Log.debugf 30 (fun k -> k "(@[cc.remove-term@ %a@])" Term.pp_debug t);
      T_tbl.remove self.tbl t);
  (* add term to the table *)
  T_tbl.add self.tbl t n;
  if Option.is_some sig0 then
    (* [n] might be merged with other equiv classes *)
    push_pending self n;
  Event.emit_iter self.on_new_term (self, n, t) ~f:(push_action_l self);
  n

(* compute the initial signature of the given e_node *)
and compute_sig0 (self : t) (n : e_node) : Signature.t option =
  (* add sub-term to [cc], and register [n] to its parents.
     Note that we return the exact sub-term, to get proper
     explanations, but we add to the sub-term's root's parent list. *)
  let deref_sub (u : Term.t) : e_node =
    let sub = add_term_rec_ self u in
    (* add [n] to [sub.root]'s parent list *)
    (let sub_r = find_ sub in
     let old_parents = sub_r.n_parents in
     if Bag.is_empty old_parents then
       (* first time it has parents: tell watchers that this is a subterm *)
       Event.emit_iter self.on_is_subterm (self, sub, u) ~f:(push_action_l self);
     on_backtrack self (fun () -> sub_r.n_parents <- old_parents);
     sub_r.n_parents <- Bag.cons n sub_r.n_parents);
    sub
  in
  let[@inline] return x = Some x in
  match self.view_as_cc n.n_term with
  | Bool _ | Opaque _ -> None
  | Eq (a, b) ->
    let a = deref_sub a in
    let b = deref_sub b in
    return @@ CC_view.Eq (a, b)
  | Not u -> return @@ CC_view.Not (deref_sub u)
  | App_fun (f, args) ->
    let args = List.map deref_sub args in
    if args <> [] then
      return @@ CC_view.App_fun (f, args)
    else
      None
  | App_ho (f, a) ->
    let f = deref_sub f in
    let a = deref_sub a in
    return @@ CC_view.App_ho (f, a)
  | If (a, b, c) -> return @@ CC_view.If (deref_sub a, deref_sub b, deref_sub c)

let[@inline] add_term self t : e_node = add_term_rec_ self t
let mem_term = mem

let set_as_lit self (n : e_node) (lit : Lit.t) : unit =
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
    Lit.t list * Proof_term.step_id =
  let { Expl_state.lits; th_lemmas = _ } = st in
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
  | CT_act (Handler_action.Act_merge (t, u, e)) -> task_merge_ self t u e
  | CT_act (Handler_action.Act_propagate (lit, reason)) ->
    (* will return this propagation to the caller *)
    Vec.push self.res_acts (Result_action.Act_propagate { lit; reason })

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
         C1: Proof_trace.true_neq_false
         C2: lemma [lits |- true=false]  (and resolve on theory proofs)
         C3: r1 C1 C2
      *)
      let expl_st = Expl_state.create () in
      explain_decompose_expl self expl_st e_ab;
      explain_equal_rec_ self expl_st a ra;
      explain_equal_rec_ self expl_st b rb;

      (* regular conflict *)
      let lits, pr = lits_and_proof_of_expl self expl_st in
      raise_conflict_ self ~th:!th (List.rev_map Lit.neg lits) pr
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

    merge_bool ra a rb b;
    merge_bool rb b ra a;

    (* perform [union r_from r_into] *)
    Log.debugf 15 (fun k ->
        k "(@[cc.merge@ :from %a@ :into %a@])" E_node.pp r_from E_node.pp r_into);

    (* call [on_pre_merge] functions, and merge theory data items *)
    (* explanation is [a=ra & e_ab & b=rb] *)
    (let expl = Expl.mk_list [ e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb ] in

     let handle_act = function
       | Ok l -> push_action_l self l
       | Error (Handler_action.Conflict expl) ->
         raise_conflict_from_expl self expl
     in

     Event.emit_iter self.on_pre_merge
       (self, r_into, r_from, expl)
       ~f:handle_act;
     Event.emit_iter self.on_pre_merge2
       (self, r_into, r_from, expl)
       ~f:handle_act);

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
         E_node.Internal_.iter_class_ r_from (fun u -> u.n_root <- r_from);
         r_into.n_size <- r_into.n_size - r_from.n_size));

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
        let reason () =
          (* true literals explaining why t1=t2 *)
          let guard = st.lits in
          (* get a proof of [guard /\ ¬lit] being absurd, to propagate [lit] *)
          Expl_state.add_lit st (Lit.neg lit);
          let _, pr = lits_and_proof_of_expl self st in
          guard, pr
        in
        Vec.push self.res_acts (Result_action.Act_propagate { lit; reason });
        Event.emit_iter self.on_propagate (self, lit, reason)
          ~f:(push_action_l self);
        Stat.incr self.count_props
      | _ -> ())

(* raise a conflict from an explanation, typically from an event handler.
   Raises E_confl with a result conflict. *)
and raise_conflict_from_expl self (expl : Expl.t) : 'a =
  Log.debugf 5 (fun k ->
      k "(@[cc.theory.raise-conflict@ :expl %a@])" Expl.pp expl);
  let st = Expl_state.create () in
  explain_decompose_expl self st expl;
  let lits, pr = lits_and_proof_of_expl self st in
  let c = List.rev_map Lit.neg lits in
  let th = st.th_lemmas <> [] in
  raise_conflict_ self ~th c pr

let add_iter self it : unit = it (fun t -> ignore @@ add_term_rec_ self t)

let push_level (self : t) : unit =
  assert (not self.in_loop);
  Backtrack_stack.push_level self.undo

let pop_levels (self : t) n : unit =
  assert (not self.in_loop);
  Vec.clear self.pending;
  Vec.clear self.combine;
  Log.debugf 15 (fun k ->
      k "(@[cc.pop-levels %d@ :n-lvls %d@])" n
        (Backtrack_stack.n_levels self.undo));
  Backtrack_stack.pop_levels self.undo n ~f:(fun f -> f ());
  ()

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
  match self.view_as_cc t with
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

let merge self n1 n2 expl =
  assert (not self.in_loop);
  Log.debugf 5 (fun k ->
      k "(@[cc.theory.merge@ :n1 %a@ :n2 %a@ :expl %a@])" E_node.pp n1 E_node.pp
        n2 Expl.pp expl);
  assert (Term.equal (Term.ty n1.n_term) (Term.ty n2.n_term));
  merge_classes self n1 n2 expl

let merge_t self t1 t2 expl =
  merge self (add_term self t1) (add_term self t2) expl

let explain_eq self n1 n2 : Resolved_expl.t =
  let st = Expl_state.create () in
  explain_equal_rec_ self st n1 n2;
  (* FIXME: also need to return the proof? *)
  Expl_state.to_resolved_expl st

let explain_expl (self : t) expl : Resolved_expl.t =
  let expl_st = Expl_state.create () in
  explain_decompose_expl self expl_st expl;
  Expl_state.to_resolved_expl expl_st

let[@inline] on_pre_merge self = Event.of_emitter self.on_pre_merge
let[@inline] on_pre_merge2 self = Event.of_emitter self.on_pre_merge2
let[@inline] on_post_merge self = Event.of_emitter self.on_post_merge
let[@inline] on_new_term self = Event.of_emitter self.on_new_term
let[@inline] on_conflict self = Event.of_emitter self.on_conflict
let[@inline] on_propagate self = Event.of_emitter self.on_propagate
let[@inline] on_is_subterm self = Event.of_emitter self.on_is_subterm

let create_ ?(stat = Stat.global) ?(size = `Big) (tst : Term.store)
    (proof : Proof_trace.t) ~view_as_cc : t =
  let size =
    match size with
    | `Small -> 128
    | `Big -> 2048
  in
  let bitgen = Bits.mk_gen () in
  let field_marked_explain = Bits.mk_field bitgen in
  let rec cc =
    {
      view_as_cc;
      tst;
      proof;
      tbl = T_tbl.create size;
      signatures_tbl = Sig_tbl.create size;
      bitgen;
      on_pre_merge = Event.Emitter.create ();
      on_pre_merge2 = Event.Emitter.create ();
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
    }
  and true_ = lazy (add_term cc (Term.true_ tst))
  and false_ = lazy (add_term cc (Term.false_ tst)) in
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

let check self : Result_action.or_conflict =
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

(** Arguments to a congruence closure's implementation *)
module type ARG = sig
  val view_as_cc : view_as_cc
  (** View the Term.t through the lens of the congruence closure *)
end

module type BUILD = sig
  val create :
    ?stat:Stat.t -> ?size:[ `Small | `Big ] -> Term.store -> Proof_trace.t -> t
  (** Create a new congruence closure.

      @param term_store used to be able to create new terms. All terms
      interacting with this congruence closure must belong in this term state
      as well.
  *)
end

module Make (A : ARG) : BUILD = struct
  let create ?stat ?size tst proof : t =
    create_ ?stat ?size tst proof ~view_as_cc:A.view_as_cc
end

module Default = Make (Sidekick_core.Default_cc_view)

let create (module A : ARG) ?stat ?size tst proof : t =
  create_ ?stat ?size tst proof ~view_as_cc:A.view_as_cc

let create_default = Default.create
