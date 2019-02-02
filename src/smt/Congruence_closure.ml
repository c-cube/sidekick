
open Solver_types

module N = Equiv_class

type node = N.t
type repr = N.t
type conflict = Theory.conflict

(** A signature is a shallow term shape where immediate subterms
    are representative *)
module Signature = struct
  type t = node Term.view
  include Term_cell.Make_eq(N)
end

module Sig_tbl = CCHashtbl.Make(Signature)

type explanation_thunk = explanation lazy_t

type combine_task =
  | CT_merge of node * node * explanation_thunk
  | CT_distinct of node list * int * explanation

type t = {
  tst: Term.state;
  tbl: node Term.Tbl.t;
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
  mutable ps_lits: Lit.Set.t;
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

let[@inline] is_root_ (n:node) : bool = n.n_root == n
let[@inline] size_ (r:repr) = r.n_size
let[@inline] true_ cc = Lazy.force cc.true_
let[@inline] false_ cc = Lazy.force cc.false_

let[@inline] on_backtrack cc f : unit =
  Backtrack_stack.push_if_nonzero_level cc.undo f

(* check if [t] is in the congruence closure.
   Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
let[@inline] mem (cc:t) (t:term): bool = Term.Tbl.mem cc.tbl t

(* find representative, recursively *)
let rec find_rec cc (n:node) : repr =
  if n==n.n_root then (
    n
  ) else (
    (* TODO: path compression, assuming backtracking restores equiv classes
       properly *)
    let root = find_rec cc n.n_root in
    root
  )

(* traverse the equivalence class of [n] *)
let iter_class_ (n:node) : node Sequence.t =
  fun yield ->
    let rec aux u =
      yield u;
      if u.n_next != n then aux u.n_next
    in
    aux n

(* get term that should be there *)
let[@inline] get_ cc (t:term) : node =
  try Term.Tbl.find cc.tbl t
  with Not_found ->
    Log.debugf 1 (fun k->k "(@[<hv1>cc.error@ :missing-term %a@])" Term.pp t);
    assert false

(* non-recursive, inlinable function for [find] *)
let[@inline] find st (n:node) : repr =
  if n == n.n_root then n else find_rec st n

let[@inline] find_tn cc (t:term) : repr = get_ cc t |> find cc

let[@inline] same_class cc (n1:node)(n2:node): bool =
  N.equal (find cc n1) (find cc n2)

(* print full state *)
let pp_full out (cc:t) : unit =
  let pp_next out n =
    Fmt.fprintf out "@ :next %a" N.pp n.n_next in
  let pp_root out n =
    if is_root_ n then Fmt.string out " :is-root" else Fmt.fprintf out "@ :root %a" N.pp n.n_root in
  let pp_expl out n = match n.n_expl with
    | E_none -> ()
    | E_some e ->
      Fmt.fprintf out " (@[:forest %a :expl %a@])" N.pp e.next Explanation.pp e.expl
  in
  let pp_n out n =
    Fmt.fprintf out "(@[%a%a%a%a@])" Term.pp n.n_term pp_root n pp_next n pp_expl n
  and pp_sig_e out (s,n) =
    Fmt.fprintf out "(@[<1>%a@ <--> %a%a@])" Signature.pp s N.pp n pp_root n
  in
  Fmt.fprintf out
    "(@[@{<yellow>cc.state@}@ (@[<hv>:nodes@ %a@])@ (@[<hv>:sig@ %a@])@])"
    (Util.pp_seq ~sep:" " pp_n) (Term.Tbl.values cc.tbl)
    (Util.pp_seq ~sep:" " pp_sig_e) (Sig_tbl.to_seq cc.signatures_tbl)

(* compute signature *)
let signature cc (t:term): node Term.view option =
  let find = find_tn cc in
  begin match Term.view t with
    | App_cst (_, a) when IArray.is_empty a -> None
    | App_cst (c, _) when not @@ Cst.do_cc c -> None (* no CC *)
    | App_cst (f, a) -> Some (App_cst (f, IArray.map find a)) (* FIXME: relevance? *)
    | Bool _ | If _
      -> None (* no congruence for these *)
  end

(* find whether the given (parent) term corresponds to some signature
   in [signatures_] *)
let find_by_signature cc (t:term) : repr option =
  match signature cc t with
  | None -> None
  | Some s -> Sig_tbl.get cc.signatures_tbl s

let add_signature cc (r:node): unit =
  match signature cc r.n_term with
  | None -> ()
  | Some s ->
    (* add, but only if not present already *)
    begin match Sig_tbl.find cc.signatures_tbl s with
      | exception Not_found ->
        Log.debugf 15
          (fun k->k "(@[cc.add_sig@ %a@ <--> %a@])" Signature.pp s N.pp r);
        on_backtrack cc (fun () -> Sig_tbl.remove cc.signatures_tbl s);
        Sig_tbl.add cc.signatures_tbl s r;
      | r' ->
        assert (same_class cc r r');
    end

let push_pending cc t : unit =
  if not @@ N.get_field N.field_is_pending t then (
    Log.debugf 5 (fun k->k "(@[<hv1>cc.push_pending@ %a@])" N.pp t);
    N.set_field N.field_is_pending true t;
    Vec.push cc.pending t
  )

let push_combine cc t u e : unit =
  Log.debugf 5
    (fun k->k "(@[<hv1>cc.push_combine@ :t1 %a@ :t2 %a@ :expl %a@])"
      N.pp t N.pp u Explanation.pp (Lazy.force e));
  Vec.push cc.combine @@ CT_merge (t,u,e)

(* re-root the explanation tree of the equivalence class of [n]
   so that it points to [n].
   postcondition: [n.n_expl = None] *)
let rec reroot_expl (cc:t) (n:node): unit =
  let old_expl = n.n_expl in
  begin match old_expl with
    | E_none -> () (* already root *)
    | E_some {next=u; expl=e_n_u} ->
      reroot_expl cc u;
      u.n_expl <- E_some {next=n; expl=e_n_u};
      n.n_expl <- E_none;
  end

let raise_conflict (cc:t) (acts:sat_actions) (e:conflict): _ =
  (* clear tasks queue *)
  Vec.iter (N.set_field N.field_is_pending false) cc.pending;
  Vec.clear cc.pending;
  Vec.clear cc.combine;
  let c = List.map Lit.neg e in
  acts.Msat.acts_raise_conflict c Proof_default

let[@inline] all_classes cc : repr Sequence.t =
  Term.Tbl.values cc.tbl
  |> Sequence.filter is_root_

(* distance from [t] to its root in the proof forest *)
let[@inline][@unroll 2] rec distance_to_root (n:node): int = match n.n_expl with
  | E_none -> 0
  | E_some {next=t'; _} -> 1 + distance_to_root t'

(* TODO: bool flag on nodes +  stepwise progress + cleanup *)
(* find the closest common ancestor of [a] and [b] in the proof forest *)
let find_common_ancestor (a:node) (b:node) : node =
  let d_a = distance_to_root a in
  let d_b = distance_to_root b in
  (* drop [n] nodes in the path from [t] to its root *)
  let rec drop_ n t =
    if n=0 then t
    else match t.n_expl with
      | E_none -> assert false
      | E_some {next=t'; _} -> drop_ (n-1) t'
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
      | E_none, _ | _, E_none -> assert false
      | E_some {next=a'; _}, E_some {next=b'; _} -> aux_same_dist a' b'
  in
  aux_same_dist a b

let[@inline] ps_add_obligation (cc:t) a b = Vec.push cc.ps_queue (a,b)
let[@inline] ps_add_lit ps l = ps.ps_lits <- Lit.Set.add l ps.ps_lits

let ps_clear (cc:t) =
  cc.ps_lits <- Lit.Set.empty;
  Vec.clear cc.ps_queue;
  ()

let decompose_explain cc (e:explanation): unit =
  Log.debugf 5 (fun k->k "(@[cc.decompose_expl@ %a@])" Explanation.pp e);
  begin match e with
    | E_reduction -> ()
    | E_lit lit -> ps_add_lit cc lit
    | E_lits l -> List.iter (ps_add_lit cc) l
    | E_merges l ->
      (* need to explain each merge in [l] *)
      IArray.iter (fun (t,u) -> ps_add_obligation cc t u) l
  end

(* explain why [a = parent_a], where [a -> ... -> parent_a] in the
   proof forest *)
let rec explain_along_path ps (a:node) (parent_a:node) : unit =
  if a!=parent_a then (
    match a.n_expl with
      | E_none -> assert false
      | E_some {next=next_a; expl=e_a_b} ->
        decompose_explain ps e_a_b;
        (* now prove [next_a = parent_a] *)
        explain_along_path ps next_a parent_a
  )

(* find explanation *)
let explain_loop (cc : t) : Lit.Set.t =
  while not (Vec.is_empty cc.ps_queue) do
    let a, b = Vec.pop cc.ps_queue in
    Log.debugf 5
      (fun k->k "(@[cc.explain_loop.at@ %a@ =?= %a@])" N.pp a N.pp b);
    assert (N.equal (find cc a) (find cc b));
    let c = find_common_ancestor a b in
    explain_along_path cc a c;
    explain_along_path cc b c;
  done;
  cc.ps_lits

let explain_eq_n ?(init=Lit.Set.empty) cc (n1:node) (n2:node) : Lit.Set.t =
  ps_clear cc;
  cc.ps_lits <- init;
  ps_add_obligation cc n1 n2;
  explain_loop cc

let explain_unfold ?(init=Lit.Set.empty) cc (e:explanation) : Lit.Set.t =
  ps_clear cc;
  cc.ps_lits <- init;
  decompose_explain cc e;
  explain_loop cc

(* add [tag] to [n], indicating that [n] is distinct from all the other
   nodes tagged with [tag]
   precond: [n] is a representative *)
let add_tag_n cc (n:node) (tag:int) (expl:explanation) : unit =
  assert (is_root_ n);
  if not (Util.Int_map.mem tag n.n_tags) then (
    on_backtrack cc
      (fun () -> n.n_tags <- Util.Int_map.remove tag n.n_tags);
    n.n_tags <- Util.Int_map.add tag (n,expl) n.n_tags;
  )

(* TODO: payload for set of tags *)
(* TODO: payload for mapping an equiv class to a set of literals, for bool prop *)

let relevant_subterms (t:Term.t) : Term.t Sequence.t =
  fun yield ->
    match t.term_view with
    | App_cst (c, a) when Cst.do_cc c -> IArray.iter yield a
    | Bool _ | App_cst _ -> ()
    | If (a,b,c) ->
      (* TODO: relevancy? only [a] needs be decided for now *)
      yield a;
      yield b;
      yield c

(* Checks if [ra] and [~into] have compatible normal forms and can
   be merged w.r.t. the theories.
   Side effect: also pushes sub-tasks *)
let notify_merge cc (ra:repr) ~into:(rb:repr) (e:explanation): unit =
  assert (is_root_ rb);
  match cc.on_merge with
  | Some f -> f ra rb e
  | None -> ()

(* main CC algo: add terms from [pending] to the signature table,
   check for collisions *)
let rec update_tasks (cc:t) (acts:sat_actions) : unit =
  while not (Vec.is_empty cc.pending && Vec.is_empty cc.combine) do
    Vec.iter (task_pending_ cc) cc.pending;
    Vec.clear cc.pending;
    Vec.iter (task_combine_ cc acts) cc.combine;
    Vec.clear cc.combine;
  done

and task_pending_ cc n =
  N.set_field N.field_is_pending false n;
  (* check if some parent collided *)
  begin match find_by_signature cc n.n_term with
    | None ->
      (* add to the signature table [sig(n) --> n] *)
      add_signature cc n
    | Some u when n == u -> ()
    | Some u ->
      (* [t1] and [t2] must be applications of the same symbol to
           arguments that are pairwise equal *)
      assert (n != u);
      let expl = lazy (
        match n.n_term.term_view, u.n_term.term_view with
        | App_cst (f1, a1), App_cst (f2, a2) ->
          assert (Cst.equal f1 f2);
          assert (IArray.length a1 = IArray.length a2);
          Explanation.mk_merges @@ IArray.map2 (fun u1 u2 -> add_term_rec_ cc u1, add_term_rec_ cc u2) a1 a2
        | If _, _ | App_cst _, _ | Bool _, _
          -> assert false
      ) in
      push_combine cc n u expl
  end;
  (* TODO: evaluate [(= t u) := true] when [find t==find u] *)
  (* FIXME: when to actually evaluate?
     eval_pending cc;
  *)
  ()

and[@inline] task_combine_ cc acts = function
  | CT_merge (a,b,e_ab) -> task_merge_ cc acts a b e_ab
  | CT_distinct (l,tag,e) -> task_distinct_ cc acts l tag e

(* main CC algo: merge equivalence classes in [st.combine].
   @raise Exn_unsat if merge fails *)
and task_merge_ cc acts a b e_ab : unit =
  let ra = find cc a in
  let rb = find cc b in
  if not (N.equal ra rb) then (
    assert (is_root_ ra);
    assert (is_root_ rb);
    let lazy e_ab = e_ab in
    (* We will merge [r_from] into [r_into].
       we try to ensure that [size ra <= size rb] in general, but always
       keep values as representative *)
    let r_from, r_into =
      if Term.is_value ra.n_term then rb, ra
      else if Term.is_value rb.n_term then ra, rb
      else if size_ ra > size_ rb then rb, ra
      else ra, rb
    in
    (* check we're not merging [true] and [false] *)
    if (N.equal ra (true_ cc) && N.equal rb (false_ cc)) ||
       (N.equal rb (true_ cc) && N.equal ra (false_ cc)) then (
      Log.debugf 5
        (fun k->k "(@[<hv>cc.merge.true_false_conflict@ @[:r1 %a@]@ @[:r2 %a@]@ :e_ab %a@])"
          N.pp ra N.pp rb Explanation.pp e_ab);
      let lits = explain_unfold cc e_ab in
      let lits = explain_eq_n ~init:lits cc a ra in
      let lits = explain_eq_n ~init:lits cc b rb in
      raise_conflict cc acts @@ Lit.Set.elements lits
    );
    (* update set of tags the new node cannot be equal to *)
    let new_tags =
      Util.Int_map.union
        (fun _i (n1,e1) (n2,e2) ->
           (* both maps contain same tag [_i]. conflict clause:
               [e1 & e2 & e_ab] impossible *)
           Log.debugf 5
             (fun k->k "(@[<hv>cc.merge.distinct_conflict@ :tag %d@ \
                        @[:r1 %a@ :e1 %a@]@ @[:r2 %a@ :e2 %a@]@ :e_ab %a@])"
                 _i N.pp n1 Explanation.pp e1
                 N.pp n2 Explanation.pp e2 Explanation.pp e_ab);
           let lits = explain_unfold cc e1 in
           let lits = explain_unfold ~init:lits cc e2 in
           let lits = explain_unfold ~init:lits cc e_ab in
           let lits = explain_eq_n ~init:lits cc a n1 in
           let lits = explain_eq_n ~init:lits cc b n2 in
           raise_conflict cc acts @@ Lit.Set.elements lits)
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
      (* for each node in [r_from]'s class:
         - make it point to [r_into]
         - push it into [st.pending] *)
      iter_class_ r_from
        (fun u ->
           assert (u.n_root == r_from);
           on_backtrack cc (fun () -> u.n_root <- r_from);
           u.n_root <- r_into;
           Bag.to_seq u.n_parents
             (fun parent -> push_pending cc parent));
      (* now merge the classes *)
      let r_into_old_tags = r_into.n_tags in
      let r_into_old_next = r_into.n_next in
      let r_from_old_next = r_from.n_next in
      on_backtrack cc
        (fun () ->
           Log.debugf 15
             (fun k->k "(@[cc.undo_merge@ :from %a :into %a@])"
                 Term.pp r_from.n_term Term.pp r_into.n_term);
           r_into.n_next <- r_into_old_next;
           r_from.n_next <- r_from_old_next;
           r_into.n_tags <- r_into_old_tags);
      r_into.n_tags <- new_tags;
      r_into.n_next <- r_from_old_next;
      r_from.n_next <- r_into_old_next;
    end;
    (* update explanations (a -> b), arbitrarily.
       Note that here we merge the classes by adding a bridge between [a]
       and [b], not their roots. *)
    begin
      reroot_expl cc a;
      assert (a.n_expl = E_none);
      (* on backtracking, link may be inverted, but we delete the one
         that bridges between [a] and [b] *)
      on_backtrack cc
        (fun () -> match a.n_expl, b.n_expl with
           | E_some e, _ when N.equal e.next b -> a.n_expl <- E_none
           | _, E_some e when N.equal e.next a -> b.n_expl <- E_none
           | _ -> assert false);
      a.n_expl <- E_some {next=b; expl=e_ab};
    end;
    (* notify listeners of the merge *)
    notify_merge cc r_from ~into:r_into e_ab;
  )

and task_distinct_ cc acts (l:node list) tag expl : unit =
  let l = List.map (fun n -> n, find cc n) l in
  let coll =
    Sequence.diagonal_l l
    |> Sequence.find_pred (fun ((_,r1),(_,r2)) -> N.equal r1 r2)
  in
  begin match coll with
    | Some ((n1,_r1),(n2,_r2)) ->
      (* two classes are already equal *)
      Log.debugf 5 (fun k->k "(@[cc.distinct.conflict@ %a = %a@])" N.pp n1 N.pp n2);
      let lits = explain_unfold cc expl in
      acts.Msat.acts_raise_conflict (Lit.Set.to_list lits) Proof_default
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
  iter_class_ r1
    (fun u1 ->
       (* propagate if:
          - [u1] is a proper literal
          - [t2 != r2], because that can only happen
            after an explicit merge (no way to obtain that by propagation)
       *)
       if N.get_field N.field_is_literal u1 && not (N.equal r2 t2) then (
         let lit = Lit.atom ~sign u1.n_term in
         Log.debugf 5 (fun k->k "(@[cc.bool_propagate@ %a@])" Lit.pp lit);
         (* complete explanation with the [u1=t1] chunk *)
         let expl = explain_eq_n ~init:(Lazy.force half_expl) cc u1 t1 in
         let reason = Msat.Consequence (Lit.Set.to_list expl, Proof_default) in
         acts.Msat.acts_propagate lit reason
       ))

(* add [t] to [cc] when not present already *)
and add_new_term_ cc (t:term) : node =
  assert (not @@ mem cc t);
  Log.debugf 15 (fun k->k "(@[cc.add-term@ %a@])" Term.pp t);
  let n = N.make t in
  (* how to add a subterm *)
  let add_to_parents_of_sub_node (sub:node) : unit =
    let old_parents = sub.n_parents in
    on_backtrack cc (fun () -> sub.n_parents <- old_parents);
    sub.n_parents <- Bag.cons n sub.n_parents;
  in
  (* add sub-term to [cc], and register [n] to its parents *)
  let add_sub_t (u:term) : unit =
    let n_u = add_term_rec_ cc u in
    add_to_parents_of_sub_node n_u
  in
  (* register sub-terms, add [t] to their parent list *)
  relevant_subterms t add_sub_t;
  (* remove term when we backtrack *)
  on_backtrack cc
    (fun () ->
       Log.debugf 15 (fun k->k "(@[cc.remove-term@ %a@])" Term.pp t);
       Term.Tbl.remove cc.tbl t);
  (* add term to the table *)
  Term.Tbl.add cc.tbl t n;
  (* [n] might be merged with other equiv classes *)
  push_pending cc n;
  n

(* add a term *)
and[@inline] add_term_rec_ cc t : node =
  try Term.Tbl.find cc.tbl t
  with Not_found -> add_new_term_ cc t

let check_invariants_ (cc:t) =
  Log.debug 5 "(cc.check-invariants)";
  Log.debugf 15 (fun k-> k "%a" pp_full cc);
  assert (Term.equal (Term.true_ cc.tst) (true_ cc).n_term);
  assert (Term.equal (Term.false_ cc.tst) (false_ cc).n_term);
  assert (not @@ same_class cc (true_ cc) (false_ cc));
  assert (Vec.is_empty cc.combine);
  assert (Vec.is_empty cc.pending);
  (* check that subterms are internalized *)
  Term.Tbl.iter
    (fun t n ->
       assert (Term.equal t n.n_term);
       assert (not @@ N.get_field N.field_is_pending n);
       relevant_subterms t
         (fun u -> assert (Term.Tbl.mem cc.tbl u));
       assert (N.equal n.n_root n.n_next.n_root);
       (* check proper signature.
          note that some signatures in the sig table can be obsolete (they
          were not removed) but there must be a valid, up-to-date signature for
          each term *)
       begin match signature cc t with
         | None -> ()
         | Some s ->
           Log.debugf 15 (fun k->k "(@[cc.check-sig@ %a@ :sig %a@])" Term.pp t Signature.pp s);
           (* add, but only if not present already *)
           begin match Sig_tbl.find cc.signatures_tbl s with
             | exception Not_found -> assert false
             | repr_s -> assert (same_class cc n repr_s)
           end
       end;
    )
    cc.tbl;
  ()

let[@inline] check_invariants (cc:t) : unit =
  if Util._CHECK_INVARIANTS then check_invariants_ cc

let[@inline] add cc t : node = add_term_rec_ cc t

let add_seq cc seq =
  seq (fun t -> ignore @@ add_term_rec_ cc t);
  ()

let[@inline] push_level (self:t) : unit =
  Backtrack_stack.push_level self.undo

let pop_levels (self:t) n : unit =
  Vec.iter (N.set_field N.field_is_pending false) self.pending;
  Vec.clear self.pending;
  Vec.clear self.combine;
  Log.debugf 15
    (fun k->k "(@[cc.pop-levels %d@ :n-lvls %d@])" n (Backtrack_stack.n_levels self.undo));
  Backtrack_stack.pop_levels self.undo n ~f:(fun f -> f());
  ()

(* TODO: if a lit is [= a b], merge [a] and [b];
   if it's [distinct a1…an], make them distinct, etc. etc. *)
(* assert that this boolean literal holds *)
let assert_lit cc lit : unit =
  let t = Lit.view lit in
  assert (Ty.is_prop t.term_ty);
  Log.debugf 5 (fun k->k "(@[cc.assert_lit@ %a@])" Lit.pp lit);
  let sign = Lit.sign lit in
  (* equate t and true/false *)
  let rhs = if sign then true_ cc else false_ cc in
  let n = add_term_rec_ cc t in
  (* TODO: ensure that this is O(1).
     basically, just have [n] point to true/false and thus acquire
     the corresponding value, so its superterms (like [ite]) can evaluate
     properly *)
  push_combine cc n rhs (Lazy.from_val @@ E_lit lit)

let[@inline] assert_lits cc lits : unit =
  Sequence.iter (assert_lit cc) lits

let assert_eq cc (t:term) (u:term) e : unit =
  let n1 = add_term_rec_ cc t in
  let n2 = add_term_rec_ cc u in
  if not (same_class cc n1 n2) then (
    let e = Lazy.from_val @@ Explanation.E_lits e in
    push_combine cc n1 n2 e;
  )

let assert_distinct cc (l:term list) ~neq (lit:Lit.t) : unit =
  assert (match l with[] | [_] -> false | _ -> true);
  let tag = Term.id neq in
  Log.debugf 5
    (fun k->k "(@[cc.assert_distinct@ (@[%a@])@ :tag %d@])" (Util.pp_list Term.pp) l tag);
  let l = List.map (add cc) l in
  Vec.push cc.combine @@ CT_distinct (l, tag, Explanation.lit lit)

let create ?on_merge ?(size=`Big) (tst:Term.state) : t =
  let size = match size with `Small -> 128 | `Big -> 2048 in
  let rec cc = {
    tst;
    tbl = Term.Tbl.create size;
    signatures_tbl = Sig_tbl.create size;
    on_merge;
    pending=Vec.create();
    combine=Vec.create();
    ps_lits=Lit.Set.empty;
    undo=Backtrack_stack.create();
    ps_queue=Vec.create();
    true_;
    false_;
  } and true_ = lazy (
      add_term_rec_ cc (Term.true_ tst)
    ) and false_ = lazy (
      add_term_rec_ cc (Term.false_ tst)
    )
  in
  ignore (Lazy.force true_ : node);
  ignore (Lazy.force false_ : node);
  cc

let[@inline] find_t cc t : repr =
  let n = Term.Tbl.find cc.tbl t in
  find cc n

let[@inline] check cc acts : unit =
  Log.debug 5 "(cc.check)";
  update_tasks cc acts

(* model: map each uninterpreted equiv class to some ID *)
let mk_model (cc:t) (m:Model.t) : Model.t =
  Log.debugf 15 (fun k->k "(@[cc.mk_model@ %a@])" pp_full cc);
  (* populate [repr -> value] table *)
  let t_tbl = N.Tbl.create 32 in
  (* type -> default value *)
  let ty_tbl = Ty.Tbl.create 8 in
  Term.Tbl.values cc.tbl
    (fun r ->
       if is_root_ r then (
         let t = r.n_term in
         let v = match Model.eval m t with
           | Some v -> v
           | None ->
             if same_class cc r (true_ cc) then Value.true_
             else if same_class cc r (false_ cc) then Value.false_
             else (
               Value.mk_elt
                 (ID.makef "v_%d" @@ Term.id t)
                 (Term.ty r.n_term)
             )
         in
         if not @@ Ty.Tbl.mem ty_tbl (Term.ty t) then (
           Ty.Tbl.add ty_tbl (Term.ty t) v; (* also give a value to this type *)
         );
         N.Tbl.add t_tbl r v
       ));
  (* now map every uninterpreted term to its representative's value, and
     create function tables *)
  let m, funs =
    Term.Tbl.to_seq cc.tbl
    |> Sequence.fold
      (fun (m,funs) (t,r) ->
         let r = find cc r in (* get representative *)
         match Term.view t with
         | _ when Model.mem t m -> m, funs
         | App_cst (c, args) ->
           if Model.mem t m then m, funs
           else if Cst.is_undefined c && IArray.length args > 0 then (
             (* update signature of [c] *)
             let ty = Term.ty t in
             let v = N.Tbl.find t_tbl r in
             let args =
               args
               |> IArray.map (fun t -> N.Tbl.find t_tbl @@ find_tn cc t)
               |> IArray.to_list
             in
             let ty, l = Cst.Map.get_or c funs ~default:(ty,[]) in
             m, Cst.Map.add c (ty, (args,v)::l) funs
           ) else (
             let v = N.Tbl.find t_tbl r in
             Model.add t v m, funs
           )
         | _ ->
           let v = N.Tbl.find t_tbl r in
           Model.add t v m, funs)
      (m,Cst.Map.empty)
  in
  (* get or make a default value for this type *)
  let rec get_ty_default (ty:Ty.t) : Value.t =
    match Ty.view ty with
    | Ty_prop -> Value.true_
    | Ty_atomic { def = Ty_uninterpreted _;_} ->
      (* domain element *)
      Ty.Tbl.get_or_add ty_tbl ~k:ty
        ~f:(fun ty -> Value.mk_elt (ID.makef "ty_%d" @@ Ty.id ty) ty)
    | Ty_atomic { def = Ty_def d; args; _} ->
      (* ask the theory for a default value *)
      Ty.Tbl.get_or_add ty_tbl ~k:ty
        ~f:(fun _ty ->
          let vals = List.map get_ty_default args in
          d.default_val vals)
  in
  let funs =
    Cst.Map.map
      (fun (ty,l) ->
         Model.Fun_interpretation.make ~default:(get_ty_default ty) l)
      funs
  in
  Model.add_funs funs m
