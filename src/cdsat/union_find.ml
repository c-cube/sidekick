open Sidekick_core

type expl = { merges: (Term.t * Term.t * Reason.t) list }

let pp_expl out (self : expl) : unit =
  Fmt.fprintf out "@[Expl {@ %a@]}" (Util.pp_iter Reason.pp)
    (Iter.of_list self.merges |> Iter.map (fun (_, _, r) -> r))

type e_node = {
  n_term: Term.t;
  mutable n_root: e_node;
      (** representative of congruence class (itself if a representative) *)
  mutable n_next: e_node;  (** pointer to next element of congruence class *)
  mutable n_size: int;  (** size of the class *)
  mutable n_expl: explanation_forest_link;
      (** the rooted forest for explanations *)
}
(** A node of the congruence closure.
      An equivalence class is represented by its "root" element,
      the representative. *)

and explanation_forest_link =
  | FL_none
  | FL_some of { next: e_node; expl: expl }

type t = {
  nodes: e_node Term.Tbl.t;
  undo: (unit -> unit) Backtrack_stack.t;
  on_changed: (Term.t, unit) Event.Emitter.t;
  changed: (Term.t, unit) Event.t;
}

let[@inline] on_changed self = self.changed

let create () : t =
  let on_changed = Event.Emitter.create () in
  {
    nodes = Term.Tbl.create 32;
    undo = Backtrack_stack.create ();
    on_changed;
    changed = Event.of_emitter on_changed;
  }

let add_term_ (self : t) (t : Term.t) : e_node =
  try Term.Tbl.find self.nodes t
  with Not_found ->
    let rec n =
      { n_term = t; n_root = n; n_next = n; n_size = 1; n_expl = FL_none }
    in
    Term.Tbl.add self.nodes t n;
    (* remove term when we backtrack *)
    Backtrack_stack.push self.undo (fun () -> Term.Tbl.remove self.nodes t);
    n

let[@unroll 2] rec find_ (n : e_node) : e_node =
  if n != n.n_next then (
    let root = find_ n.n_next in
    n.n_next <- root;
    root
  ) else
    n

let[@inline] find self t : Term.t =
  let n = add_term_ self t in
  (find_ n).n_term

let are_equal self t u : bool =
  let nt = add_term_ self t in
  let nu = add_term_ self u in
  find_ nt == find_ nu

let iter_class_ (n0 : e_node) k =
  let n = ref n0 in
  while
    k !n;
    n := !n.n_next;
    !n != n0
  do
    ()
  done

let[@inline] swap_next n1 n2 : unit =
  let tmp = n1.n_next in
  n1.n_next <- n2.n_next;
  n2.n_next <- tmp

(*
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
      let pr = Proof.Tracer.add_step self.proof pr in
      let c = List.rev_map Lit.neg lits in
      raise_conflict_ self ~th:!th c ~cc_lemma:c pr
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

    (* call [on_pre_merge] functions, and merge theory data items.
       explanation is [a=ra & e_ab & b=rb] *)
    (let expl = Expl.mk_list [ e_ab; Expl.mk_merge a ra; Expl.mk_merge b rb ] in

     let handle_act = function
       | Ok l -> push_action_l self l
       | Error (Handler_action.Conflict { t; u; expl; pr }) ->
         raise_conflict_from_expl self t u expl pr
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
     let r_into_old_parents = r_into.n_parents in
     let r_into_old_bits = r_into.n_bits in
     (* swap [into.next] and [from.next], merging the classes *)
     E_node.swap_next r_into r_from;
     r_into.n_parents <- Bag.append r_into.n_parents r_from.n_parents;
     r_into.n_size <- r_into.n_size + r_from.n_size;
     r_into.n_bits <- Bits.merge r_into.n_bits r_from.n_bits;
     (* on backtrack, unmerge classes and restore the pointers to [r_from] *)
     on_backtrack self (fun () ->
         Log.debugf 30 (fun k ->
             k "(@[cc.undo_merge@ :from %a@ :into %a@])" E_node.pp r_from
               E_node.pp r_into);
         r_into.n_bits <- r_into_old_bits;
         (* un-merge the classes *)
         E_node.swap_next r_into r_from;
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
    on_backtrack self (fun () ->
        (* on backtracking, link may be inverted, but we delete the one
           that bridges between [a] and [b] *)
        match a.n_expl, b.n_expl with
        | FL_some e, _ when E_node.equal e.next b -> a.n_expl <- FL_none
        | _, FL_some e when E_node.equal e.next a -> b.n_expl <- FL_none
        | _ -> assert false);
    a.n_expl <- FL_some { next = b; expl = e_ab };
    (* call [on_post_merge] *)
    Event.emit_iter self.on_post_merge (self, r_into, r_from)
      ~f:(push_action_l self)
  )
  *)

(** re-root the explanation tree of the equivalence class of [n]
   so that it points to [n].
   postcondition: [n.n_expl = None] *)
let[@unroll 2] rec reroot_expl (n : e_node) : unit =
  match n.n_expl with
  | FL_none -> () (* already root *)
  | FL_some { next = u; expl = e_n_u } ->
    (* reroot to [u], then invert link between [u] and [n] *)
    reroot_expl u;
    u.n_expl <- FL_some { next = n; expl = e_n_u };
    n.n_expl <- FL_none

let merge self a b r : unit =
  let na = find_ @@ add_term_ self a in
  let nb = find_ @@ add_term_ self b in
  if na != nb then (
    let n_big, n_small =
      if na.n_size > nb.n_size then
        na, nb
      else
        nb, na
    in
    Backtrack_stack.push self.undo (fun () -> () (* TODO *));
    n_small.n_root <- n_big;

    (* add explanation *)
    reroot_expl n_small;
    assert (n_small.n_expl = FL_none);
    Backtrack_stack.push self.undo (fun () ->
        (* on backtracking, link may be inverted, but we delete the one
           that bridges between the two nodes *)
        match n_small.n_expl, n_big.n_expl with
        | FL_some e, _ when e.next == n_big -> n_small.n_expl <- FL_none
        | _, FL_some e when e.next == n_small -> n_big.n_expl <- FL_none
        | _ -> assert false);
    n_small.n_expl <- FL_some { next = n_big; expl = r };

    (* notify subscribers *)
    iter_class_ n_small (fun n -> Event.Emitter.emit self.on_changed n.n_term);

    (* merge classes *)
    swap_next n_small n_big
  )

let push_level self = Backtrack_stack.push_level self.undo
let pop_levels self n = Backtrack_stack.pop_levels self n ~f:(fun k -> k ())
let n_levels self = Backtrack_stack.n_levels self.undo

(* TODO
   module Expl_state = struct
     type t = {
       mutable lits: Lit.t list;
       mutable th_lemmas:
         (Lit.t * (Lit.t * Lit.t list) list * Proof.Pterm.delayed) list;
       mutable local_gen: int;
     }

     let create () : t = { lits = []; th_lemmas = []; local_gen = -2 }
     let[@inline] copy self : t = { self with lits = self.lits }
     let[@inline] add_lit (self : t) lit = self.lits <- lit :: self.lits

     let[@inline] new_local_id (self : t) : Proof.Pterm.local_ref =
       let n = self.local_gen in
       self.local_gen <- n - 1;
       n

     let[@inline] add_th (self : t) lit hyps pr : unit =
       self.th_lemmas <- (lit, hyps, pr) :: self.th_lemmas

     let merge self other =
       let { lits = o_lits; th_lemmas = o_lemmas; local_gen = o_l } = other in
       self.lits <- List.rev_append o_lits self.lits;
       self.th_lemmas <- List.rev_append o_lemmas self.th_lemmas;
       self.local_gen <- min self.local_gen o_l;
       ()

     (* proof of [\/_i ¬lits[i]] *)
     let proof_of_th_lemmas (self : t) : Proof.Pterm.delayed =
       Proof.Pterm.delay @@ fun () ->
       let bs = ref [] in
       let bind (t : Proof.Pterm.t) : Proof.Pterm.local_ref =
         let n = new_local_id self in
         bs := (n, t) :: !bs;
         n
       in

       let p_lits1 = List.rev_map Lit.neg self.lits in
       let p_lits2 =
         self.th_lemmas |> List.rev_map (fun (lit_t_u, _, _) -> Lit.neg lit_t_u)
       in
       let p_cc = Proof.Core_rules.lemma_cc (List.rev_append p_lits1 p_lits2) in
       let resolve_with_th_proof pr (lit_t_u, sub_proofs, pr_th) =
         let pr_th = pr_th () in
         (* pr_th: [sub_proofs |- t=u].
             now resolve away [sub_proofs] to get literals that were
             asserted in the congruence closure *)
         let pr_th =
           List.fold_left
             (fun pr_th (lit_i, hyps_i) ->
               (* [hyps_i |- lit_i] *)
               let lemma_i =
                 bind
                 @@ Proof.Core_rules.lemma_cc (lit_i :: List.rev_map Lit.neg hyps_i)
               in
               (* resolve [lit_i] away. *)
               Proof.Core_rules.proof_res ~pivot:(Lit.term lit_i) lemma_i
                 (bind pr_th))
             pr_th sub_proofs
         in
         Proof.Core_rules.proof_res ~pivot:(Lit.term lit_t_u) (bind pr_th)
           (bind pr)
       in
       (* resolve with theory proofs responsible for some merges, if any. *)
       let body = List.fold_left resolve_with_th_proof p_cc self.th_lemmas in
       Proof.Pterm.let_ (List.rev !bs) body

     let to_resolved_expl (self : t) : Resolved_expl.t =
       (* FIXME: package the th lemmas too *)
       let { lits; th_lemmas = _; local_gen = _ } = self in
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
         Error.errorf "expl: cannot find e_node(s) for %a, %a" Term.pp a Term.pp b)
     | E_and (a, b) ->
       explain_decompose_expl self st a;
       explain_decompose_expl self st b

   and explain_expls self (es : explanation list) : Expl_state.t =
     let st = Expl_state.create () in
     List.iter (explain_decompose_expl self st) es;
     st

   and explain_equal_rec_ (cc : t) (st : Expl_state.t) (a : e_node) (b : e_node) :
       unit =
     if a != b then (
       Log.debugf 5 (fun k ->
           k "(@[cc.explain_loop.at@ %a@ =?= %a@])" E_node.pp a E_node.pp b);
       assert (E_node.equal (find_ a) (find_ b));
       let ancestor = find_common_ancestor cc a b in
       explain_along_path cc st a ancestor;
       explain_along_path cc st b ancestor
     )

   (* explain why [a = target], where [a -> ... -> target] in the
      proof forest *)
   and explain_along_path self (st : Expl_state.t) (a : e_node) (target : e_node) :
       unit =
     let rec aux n =
       if n != target then (
         match n.n_expl with
         | FL_none -> assert false
         | FL_some { next = next_a; expl } ->
           (* prove [a = next_n] *)
           explain_decompose_expl self st expl;
           (* now prove [next_a = target] *)
           aux next_a
       )
     in
     aux a
*)
