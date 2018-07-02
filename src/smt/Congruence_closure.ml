
module Vec = Sidekick_sat.Vec
module Log = Sidekick_sat.Log
open Solver_types

type node = Equiv_class.t
type repr = Equiv_class.t
type conflict = Theory.conflict

(** A signature is a shallow term shape where immediate subterms
    are representative *)
module Signature = struct
  type t = node Term.view
  include Term_cell.Make_eq(Equiv_class)
end

module Sig_tbl = CCHashtbl.Make(Signature)

module type ACTIONS = sig
  val on_backtrack: (unit -> unit) -> unit
  (** Register a callback to be invoked upon backtracking below the current level *)

  val on_merge: repr -> repr -> explanation -> unit
  (** Call this when two classes are merged *)

  val raise_conflict: conflict -> 'a
  (** Report a conflict *)

  val propagate: Lit.t -> Lit.t list -> unit
  (** Propagate a literal *)
end

type actions = (module ACTIONS)

type task =
  | T_pending of node
  | T_merge of node * node * explanation

type t = {
  tst: Term.state;
  acts: actions;
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
  tasks: task Vec.t;
  (* tasks to perform *)
  mutable ps_lits: Lit.Set.t;
  (* proof state *)
  ps_queue: (node*node) Vec.t;
  (* pairs to explain *)
  mutable true_ : node;
  mutable false_ : node;
}
(* TODO: an additional union-find to keep track, for each term,
   of the terms they are known to be equal to, according
   to the current explanation. That allows not to prove some equality
   several times.
   See "fast congruence closure and extensions", Nieuwenhis&al, page 14 *)

let[@inline] on_backtrack cc f : unit =
  let (module A) = cc.acts in
  A.on_backtrack f

let[@inline] is_root_ (n:node) : bool = n.n_root == n

let[@inline] size_ (r:repr) =
  assert (is_root_ r);
  Bag.size r.n_parents

(* check if [t] is in the congruence closure.
   Invariant: [in_cc t ∧ do_cc t => forall u subterm t, in_cc u] *)
let[@inline] mem (cc:t) (t:term): bool = Term.Tbl.mem cc.tbl t

(* TODO: remove path compression, point to new root explicitely during `union` *)

(* find representative, recursively, and perform path compression *)
let rec find_rec cc (n:node) : repr =
  if n==n.n_root then (
    n
  ) else (
    let old_root = n.n_root in
    let root = find_rec cc old_root in
    (* path compression *)
    if root != old_root then (
      on_backtrack cc (fun () -> n.n_root <- old_root);
      n.n_root <- root;
    );
    root
  )

let[@inline] true_ cc = cc.true_
let[@inline] false_ cc = cc.false_

(* get term that should be there *)
let[@inline] get_ cc (t:term) : node =
  try Term.Tbl.find cc.tbl t
  with Not_found ->
    Log.debugf 1 (fun k->k "(@[<hv1>cc.error: missing@ %a@])" Term.pp t);
    assert false

(* non-recursive, inlinable function for [find] *)
let[@inline] find st (n:node) : repr =
  if n == n.n_root then n else find_rec st n

let[@inline] find_tn cc (t:term) : repr = get_ cc t |> find cc

let[@inline] same_class cc (n1:node)(n2:node): bool =
  Equiv_class.equal (find cc n1) (find cc n2)

(* compute signature *)
let signature cc (t:term): node Term.view option =
  let find = find_tn cc in
  begin match Term.view t with
    | App_cst (_, a) when IArray.is_empty a -> None
    | App_cst (c, _) when not @@ Cst.do_cc c -> None (* no CC *)
    | App_cst (f, a) -> App_cst (f, IArray.map find a) |> CCOpt.return (* FIXME: relevance *)
    | Bool _ | If _
      -> None (* no congruence for these *)
   end

(* find whether the given (parent) term corresponds to some signature
   in [signatures_] *)
let find_by_signature cc (t:term) : repr option =
  match signature cc t with
  | None -> None
  | Some s -> Sig_tbl.get cc.signatures_tbl s

let add_signature cc (t:term) (r:node): unit =
  match signature cc t with
  | None -> ()
  | Some s ->
    (* add, but only if not present already *)
    begin match Sig_tbl.find cc.signatures_tbl s with
      | exception Not_found ->
        on_backtrack cc (fun () -> Sig_tbl.remove cc.signatures_tbl s);
        Sig_tbl.add cc.signatures_tbl s r;
      | r' ->
        assert (same_class cc r r');
    end

let push_pending cc t : unit =
  if not @@ Equiv_class.get_field Equiv_class.field_is_pending t then (
    Log.debugf 5 (fun k->k "(@[<hv1>cc.push_pending@ %a@])" Equiv_class.pp t);
    Equiv_class.set_field Equiv_class.field_is_pending true t;
    Vec.push cc.tasks (T_pending t)
  )

let push_combine cc t u e : unit =
  Log.debugf 5
    (fun k->k "(@[<hv1>cc.push_combine@ :t1 %a@ :t2 %a@ :expl %a@])"
      Equiv_class.pp t Equiv_class.pp u Explanation.pp e);
  Vec.push cc.tasks @@ T_merge (t,u,e)

(* re-root the explanation tree of the equivalence class of [n]
   so that it points to [n].
   postcondition: [n.n_expl = None] *)
let rec reroot_expl (cc:t) (n:node): unit =
  let old_expl = n.n_expl in
  on_backtrack cc (fun () -> n.n_expl <- old_expl);
  begin match old_expl with
    | E_none -> () (* already root *)
    | E_some {next=u; expl=e_n_u} ->
      reroot_expl cc u;
      u.n_expl <- E_some {next=n; expl=e_n_u};
      n.n_expl <- E_none;
  end

let raise_conflict (cc:t) (e:conflict): _ =
  let (module A) = cc.acts in
  (* clear tasks queue *)
  Vec.iter
    (function
      | T_pending n -> Equiv_class.set_field Equiv_class.field_is_pending false n
      | T_merge _ -> ())
    cc.tasks;
  Vec.clear cc.tasks;
  A.raise_conflict e

let[@inline] all_classes cc : repr Sequence.t =
  Term.Tbl.values cc.tbl
  |> Sequence.filter is_root_

(* distance from [t] to its root in the proof forest *)
let[@inline][@unroll 2] rec distance_to_root (n:node): int = match n.n_expl with
  | E_none -> 0
  | E_some {next=t'; _} -> 1 + distance_to_root t'

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

and ps_add_obligation_t cc (t1:term) (t2:term) =
  let n1 = get_ cc t1 in
  let n2 = get_ cc t2 in
  ps_add_obligation cc n1 n2

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
    let a, b = Vec.pop_last cc.ps_queue in
    Log.debugf 5
      (fun k->k "(@[cc.explain_loop at@ %a@ %a@])" Equiv_class.pp a Equiv_class.pp b);
    assert (Equiv_class.equal (find cc a) (find cc b));
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

let explain_eq_t ?(init=Lit.Set.empty) cc (t1:term) (t2:term) : Lit.Set.t =
  ps_clear cc;
  cc.ps_lits <- init;
  ps_add_obligation_t cc t1 t2;
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

(* main CC algo: add terms from [pending] to the signature table,
   check for collisions *)
let rec update_tasks (cc:t): unit =
  (* step 2 deal with pending (parent) terms whose equiv class
     might have changed *)
  while not (Vec.is_empty cc.tasks) do
    let task = Vec.pop_last cc.tasks in
    match task with 
    | T_pending n -> task_pending_ cc n
    | T_merge (t,u,expl) -> task_merge_ cc t u expl
  done

and task_pending_ cc n =
  Equiv_class.set_field Equiv_class.field_is_pending false n;
  (* check if some parent collided *)
  begin match find_by_signature cc n.n_term with
    | None ->
      (* add to the signature table [sig(n) --> n] *)
      add_signature cc n.n_term n
    | Some u when n == u -> ()
    | Some u ->
      (* must combine [t] with [r] *)
      if not @@ same_class cc n u then (
        (* [t1] and [t2] must be applications of the same symbol to
           arguments that are pairwise equal *)
        assert (n != u);
        let expl = match n.n_term.term_view, u.n_term.term_view with
          | App_cst (f1, a1), App_cst (f2, a2) ->
            assert (Cst.equal f1 f2);
            assert (IArray.length a1 = IArray.length a2);
            Explanation.mk_merges @@ IArray.map2 (fun u1 u2 -> add_ cc u1, add_ cc u2) a1 a2
          | If _, _ | App_cst _, _ | Bool _, _
            -> assert false
        in
        push_combine cc n u expl
      )
  end;
  (* FIXME: when to actually evaluate?
     eval_pending cc;
  *)
  ()

(* main CC algo: merge equivalence classes in [st.combine].
   @raise Exn_unsat if merge fails *)
and task_merge_ cc a b e_ab : unit =
  let ra = find cc a in
  let rb = find cc b in
  if not (Equiv_class.equal ra rb) then (
    assert (is_root_ ra);
    assert (is_root_ rb);
    (* We will merge [r_from] into [r_into].
       we try to ensure that [size ra <= size rb] in general *)
    let r_from, r_into = if size_ ra > size_ rb then rb, ra else ra, rb in
    let new_tags =
      Util.Int_map.union
        (fun _i (n1,e1) (n2,e2) ->
           (* both maps contain same tag [_i]. conflict clause:
               [e1 & e2 & e_ab] impossible *)
           Log.debugf 5
             (fun k->k "(@[<hv>cc.merge.distinct_conflict@ :tag %d@ \
                        @[:r1 %a@ :e1 %a@]@ @[:r2 %a@ :e2 %a@]@ :e_ab %a@])"
                 _i Equiv_class.pp n1 Explanation.pp e1
                 Equiv_class.pp n2 Explanation.pp e2 Explanation.pp e_ab);
           let lits = explain_unfold cc e1 in
           let lits = explain_unfold ~init:lits cc e2 in
           let lits = explain_unfold ~init:lits cc e_ab in
           let lits = explain_eq_n ~init:lits cc a n1 in
           let lits = explain_eq_n ~init:lits cc b n2 in
           raise_conflict cc @@ Lit.Set.elements lits)
        ra.n_tags rb.n_tags
    in
    (* remove [ra.parents] from signature, put them into [st.pending] *)
    begin
      Bag.to_seq r_from.n_parents
        (fun parent -> push_pending cc parent)
    end;
    (* perform [union ra rb] *)
    begin
      let r_into_old_parents = r_into.n_parents in
      let r_into_old_tags = r_into.n_tags in
      on_backtrack cc
        (fun () ->
           Log.debugf 15
             (fun k->k "(@[cc.undo_merge@ :of %a :into %a@])"
                 Term.pp r_from.n_term Term.pp r_into.n_term);
           r_from.n_root <- r_from;
           r_into.n_tags <- r_into_old_tags;
           r_into.n_parents <- r_into_old_parents);
      r_from.n_root <- r_into;
      r_into.n_tags <- new_tags;
      r_from.n_parents <- Bag.append r_into_old_parents r_from.n_parents;
    end;
    (* update explanations (a -> b), arbitrarily *)
    begin
      reroot_expl cc a;
      assert (a.n_expl = E_none);
      on_backtrack cc (fun () -> a.n_expl <- E_none);
      a.n_expl <- E_some {next=b; expl=e_ab};
    end;
    (* notify listeners of the merge *)
    notify_merge cc r_from ~into:r_into e_ab;
  )

(* Checks if [ra] and [~into] have compatible normal forms and can
   be merged w.r.t. the theories.
   Side effect: also pushes sub-tasks *)
and notify_merge cc (ra:repr) ~into:(rb:repr) (e:explanation): unit =
  assert (is_root_ rb);
  let (module A) = cc.acts in
  A.on_merge ra rb e

(* add [t] to [cc] when not present already *)
and add_new_term_ cc (t:term) : node =
  assert (not @@ mem cc t);
  Log.debugf 15 (fun k->k "(@[cc.add-term@ %a@])" Term.pp t);
  let n = Equiv_class.make t in
  (* how to add a subterm *)
  let add_to_parents_of_sub_node (sub:node) : unit =
    let old_parents = sub.n_parents in
    on_backtrack cc (fun () -> sub.n_parents <- old_parents);
    sub.n_parents <- Bag.cons n sub.n_parents;
    push_pending cc sub
  in
  (* add sub-term to [cc], and register [n] to its parents *)
  let add_sub_t (u:term) : unit =
    let n_u = add_ cc u in
    add_to_parents_of_sub_node n_u
  in
  (* register sub-terms, add [t] to their parent list *)
  begin match t.term_view with
    | App_cst (c, a) when Cst.do_cc c -> IArray.iter add_sub_t a
    | Bool _ | App_cst _ -> ()
    | If (a,b,c) ->
      (* TODO: relevancy? only [a] needs be decided for now *)
      add_sub_t a;
      add_sub_t b;
      add_sub_t c
  end;
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
and[@inline] add_ cc t : node =
  try Term.Tbl.find cc.tbl t
  with Not_found -> add_new_term_ cc t

let add cc t : node =
  let n = add_ cc t in
  update_tasks cc;
  n

let add_seq cc seq =
  seq (fun t -> ignore @@ add_ cc t);
  update_tasks cc

(* assert that this boolean literal holds *)
let assert_lit cc lit : unit =
  let t = Lit.view lit in
  assert (Ty.is_prop t.term_ty);
  Log.debugf 5 (fun k->k "(@[cc.assert_lit@ %a@])" Lit.pp lit);
  let sign = Lit.sign lit in
  (* equate t and true/false *)
  let rhs = if sign then true_ cc else false_ cc in
  let n = add_ cc t in
  (* TODO: ensure that this is O(1).
     basically, just have [n] point to true/false and thus acquire
     the corresponding value, so its superterms (like [ite]) can evaluate
     properly *)
  push_combine cc n rhs (E_lit lit);
  update_tasks cc

let assert_eq cc (t:term) (u:term) e : unit =
  let n1 = add_ cc t in
  let n2 = add_ cc u in
  if not (same_class cc n1 n2) then (
    let e = Explanation.E_lits e in
    push_combine cc n1 n2 e;
  );
  update_tasks cc

let assert_distinct cc (l:term list) ~neq (lit:Lit.t) : unit =
  assert (match l with[] | [_] -> false | _ -> true);
  let tag = Term.id neq in
  Log.debugf 5
    (fun k->k "(@[cc.assert_distinct@ (@[%a@])@ :tag %d@])" (Util.pp_list Term.pp) l tag);
  let l = List.map (fun t -> t, add cc t |> find cc) l in
  let coll =
    Sequence.diagonal_l l
    |> Sequence.find_pred (fun ((_,n1),(_,n2)) -> Equiv_class.equal n1 n2)
  in
  begin match coll with
    | Some ((t1,_n1),(t2,_n2)) ->
      (* two classes are already equal *)
      Log.debugf 5 (fun k->k "(@[cc.assert_distinct.conflict@ %a = %a@])" Term.pp t1 Term.pp t2);
      let lits = Lit.Set.singleton lit in
      let lits = explain_eq_t ~init:lits cc t1 t2 in
      raise_conflict cc @@ Lit.Set.to_list lits
    | None ->
      (* put a tag on all equivalence classes, that will make their merge fail *)
      List.iter (fun (_,n) -> add_tag_n cc n tag @@ Explanation.lit lit) l
  end

let create ?(size=2048) ~actions (tst:Term.state) : t =
  let nd = Equiv_class.dummy in
  let cc = {
    tst;
    acts=actions;
    tbl = Term.Tbl.create size;
    signatures_tbl = Sig_tbl.create size;
    tasks=Vec.make_empty (T_pending Equiv_class.dummy);
    ps_lits=Lit.Set.empty;
    ps_queue=Vec.make_empty (nd,nd);
    true_ = Equiv_class.dummy;
    false_ = Equiv_class.dummy;
  } in
  cc.true_ <- add cc (Term.true_ tst);
  cc.false_ <- add cc (Term.false_ tst);
  cc

let final_check cc : unit =
  Log.debug 5 "(CC.final_check)";
  update_tasks cc

(* model: map each uninterpreted equiv class to some ID *)
let mk_model (cc:t) (m:Model.t) : Model.t =
  (* populate [repr -> value] table *)
  let t_tbl = Equiv_class.Tbl.create 32 in
  (* type -> default value *)
  let ty_tbl = Ty.Tbl.create 8 in
  Term.Tbl.values cc.tbl
    (fun r ->
       if is_root_ r then (
         let t = r.n_term in
         let v = match Model.eval m t with
           | Some v -> v
           | None ->
             if same_class cc r cc.true_ then Value.true_
             else if same_class cc r cc.false_ then Value.false_
             else (
               Value.mk_elt
                 (ID.makef "v_%d" @@ Term.id t)
                 (Term.ty r.n_term)
             )
         in
         if not @@ Ty.Tbl.mem ty_tbl (Term.ty t) then (
           Ty.Tbl.add ty_tbl (Term.ty t) v; (* also give a value to this type *)
         );
         Equiv_class.Tbl.add t_tbl r v
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
             let v = Equiv_class.Tbl.find t_tbl r in
             let args =
               args
               |> IArray.map (fun t -> Equiv_class.Tbl.find t_tbl @@ find_tn cc t)
               |> IArray.to_list
             in
             let ty, l = Cst.Map.get_or c funs ~default:(ty,[]) in
             m, Cst.Map.add c (ty, (args,v)::l) funs
           ) else (
             let v = Equiv_class.Tbl.find t_tbl r in
             Model.add t v m, funs
           )
         | _ ->
           let v = Equiv_class.Tbl.find t_tbl r in
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
