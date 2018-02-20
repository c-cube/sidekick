(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

module Make
    (St : Solver_types.S)
    (Th : Theory_intf.S with type formula = St.formula
                             and type proof = St.proof)
= struct
  module Proof = Res.Make(St)

  open St

  module H = Heap.Make(struct
    type t = St.var
    let[@inline] cmp i j = Var.weight j < Var.weight i (* comparison by weight *)
    let dummy = St.Var.dummy
    let idx = St.Var.idx
    let set_idx = St.Var.set_idx
  end)

  exception Sat
  exception Unsat
  exception UndecidedLit
  exception Restart
  exception Conflict of clause

  let var_decay : float = 1. /. 0.95
  (* inverse of the activity factor for variables. Default 1/0.999 *)

  let clause_decay : float = 1. /. 0.999
  (* inverse of the activity factor for clauses. Default 1/0.95 *)

  let restart_first : int = 100
  (* intial restart limit *)

  let learntsize_factor : float = 1. /. 3.
  (* initial limit for the number of learnt clauses, 1/3 of initial
      number of clauses by default *)

  let restart_inc : float = 1.5
  (* multiplicative factor for restart limit, default 1.5 *)

  let learntsize_inc : float = 1.1
  (* multiplicative factor for [learntsize_factor] at each restart, default 1.1 *)

  (* Singleton type containing the current state *)
  type t = {
    st : St.t;

    th: Th.t lazy_t;

    (* Clauses are simplified for eficiency purposes. In the following
       vectors, the comments actually refer to the original non-simplified
       clause. *)

    clauses_hyps : clause Vec.t;
    (* clauses added by the user *)
    clauses_learnt : clause Vec.t;
    (* learnt clauses (tautologies true at any time, whatever the user level) *)
    clauses_temp : clause Vec.t;
    (* Temp clauses, corresponding to the local assumptions. This vec is used
       only to have an efficient way to access the list of local assumptions. *)

    mutable unsat_conflict : clause option;
    (* conflict clause at [base_level], if any *)
    mutable next_decision : atom option;
    (* When the last conflict was a semantic one, this stores the next decision to make *)

    trail : atom Vec.t;
    (* decision stack + propagated elements (atoms or assignments). *)

    elt_levels : int Vec.t;
    (* decision levels in [trail]  *)

    user_levels : int Vec.t;
    (* user levels in [clause_tmp] *)

    backtrack_levels : int Vec.t;
    (* user levels in [backtrack] *)

    backtrack : (unit -> unit) Vec.t;
    (** Actions to call when backtracking *)

    to_redo_after_backtrack: (unit -> unit) Vec.t;
    (** Actions to re-do after backtracking *)

    mutable th_head : int;
    (* Start offset in the queue {!trail} of
       unit facts not yet seen by the theory. *)
    mutable elt_head : int;
    (* Start offset in the queue {!trail} of
       unit facts to propagate, within the trail *)

    (* invariant:
       - during propagation, th_head <= elt_head
       - then, once elt_head reaches length trail, Th.assume is
         called so that th_head can catch up with elt_head
       - this is repeated until a fixpoint is reached;
       - before a decision (and after the fixpoint),
         th_head = elt_head = length trail
    *)

    order : H.t;
    (* Heap ordered by variable activity *)

    mutable var_incr : float;
    (* increment for variables' activity *)

    mutable clause_incr : float;
    (* increment for clauses' activity *)

    mutable dirty: bool;
    (* is there a [pop()] on top of the stack for examining
       current model/proof? *)
  }

  (* Starting environment. *)
  let create_ ~st ~size_trail ~size_lvl th : t = {
    st;
    th;
    unsat_conflict = None;
    next_decision = None;

    clauses_hyps = Vec.make 0 Clause.dummy;
    clauses_learnt = Vec.make 0 Clause.dummy;
    clauses_temp = Vec.make 0 Clause.dummy;

    th_head = 0;
    elt_head = 0;

    trail = Vec.make size_trail Atom.dummy;
    elt_levels = Vec.make size_lvl (-1);
    backtrack_levels = Vec.make size_lvl (-1);
    backtrack = Vec.make size_lvl (fun () -> ());
    to_redo_after_backtrack = Vec.make 10 (fun () -> ());
    user_levels = Vec.make 0 (-1);

    order = H.create();

    var_incr = 1.;
    clause_incr = 1.;
    dirty=false;
  }

  let[@inline] theory st = Lazy.force st.th
  let[@inline] on_backtrack st f : unit = Vec.push st.backtrack f
  let[@inline] at_level_0 st : bool = Vec.is_empty st.backtrack_levels

  (* schedule [f] as a backtrack action, iff the solver's current
     level is not 0. *)
  let[@inline] on_backtrack_if_not_at_0 st f =
    if not (at_level_0 st) then (
      on_backtrack st f;
    )

  let[@inline] st t = t.st
  let[@inline] nb_clauses st = Vec.size st.clauses_hyps
  let[@inline] decision_level st = Vec.size st.elt_levels
  let[@inline] base_level st = Vec.size st.user_levels
  let[@inline] mk_atom st (f:St.formula) : atom = Atom.make st.st f

  (* [redo_down_to_level_0 f ~undo] performs [f] now. Upon backtracking
     before current level, some undo actions scheduled by [f]
     might run;
     later [f] will be called again
     to re-perform the action, and this cycle [f(); backtrack; f(); …] is
     done until we backtrack at level 0.
     Once at level 0, [f()] is called and will never be undone again.
     *)
  let rec redo_down_to_level_0 (st:t) (f:unit->unit) : unit =
    if not (at_level_0 st) then (
      on_backtrack st
        (fun () ->
           Vec.push st.to_redo_after_backtrack
             (fun () -> redo_down_to_level_0 st f))
    );
    f()

  (* Misc functions *)
  let to_float = float_of_int
  let to_int = int_of_float

  (* Are the assumptions currently unsat ? *)
  let[@inline] is_unsat st =
    match st.unsat_conflict with
    | Some _ -> true
    | None -> false

  (* Variable and literal activity.
     Activity is used to decide on which variable to decide when propagation
     is done. Uses a heap (implemented in {!Heap}), to keep track of variable activity.
  *)
  let insert_var_order st (v:var) : unit =
    if not (Var.in_heap v) then (
      (* remove variable when we backtrack *)
      on_backtrack_if_not_at_0 st (fun () -> H.remove st.order v);
      H.insert st.order v;
    )

  let new_atom ~permanent st (p:formula) : unit =
    let a = mk_atom st p in
    if permanent then (
      (* TODO: also internalize term… *)
      redo_down_to_level_0 st
        (fun () -> insert_var_order st a.var)
    ) else (
      insert_var_order st a.var
    )

  (* Rather than iterate over all the heap when we want to decrease all the
     variables/literals activity, we instead increase the value by which
     we increase the activity of 'interesting' var/lits. *)
  let[@inline] var_decay_activity st =
    st.var_incr <- st.var_incr *. var_decay

  let[@inline] clause_decay_activity st =
    st.clause_incr <- st.clause_incr *. clause_decay

  (* increase activity of [v] *)
  let var_bump_activity st v =
    v.v_weight <- v.v_weight +. st.var_incr;
    if v.v_weight > 1e100 then (
      for i = 0 to St.nb_elt st.st - 1 do
        Var.set_weight (St.get_elt st.st i) ((Var.weight (St.get_elt st.st i)) *. 1e-100)
      done;
      st.var_incr <- st.var_incr *. 1e-100;
    );
    if H.in_heap v then (
      H.decrease st.order v
    )

  (* increase activity of clause [c] *)
  let clause_bump_activity st (c:clause) : unit =
    c.activity <- c.activity +. st.clause_incr;
    if c.activity > 1e20 then (
      for i = 0 to Vec.size st.clauses_learnt - 1 do
        (Vec.get st.clauses_learnt i).activity <-
          (Vec.get st.clauses_learnt i).activity *. 1e-20;
      done;
      st.clause_incr <- st.clause_incr *. 1e-20
    )

  (* Simplification of clauses.

     When adding new clauses, it is desirable to 'simplify' them, i.e
     minimize the amount of literals in it, because it greatly reduces
     the search space for new watched literals during propagation.
     Additionally, we have to partition the lits, to ensure the watched
     literals (which are the first two lits of the clause) are appropriate.
     Indeed, it is better to watch true literals, and then unassigned literals.
     Watching false literals should be a last resort, and come with constraints
     (see {!add_clause}).
  *)
  exception Trivial

  (* [arr_to_list a i] converts [a.(i), ... a.(length a-1)] into a list *)
  let arr_to_list arr i : _ list =
    if i >= Array.length arr then []
    else Array.to_list (Array.sub arr i (Array.length arr - i))

  (* Eliminates atom doublons in clauses *)
  let eliminate_duplicates clause : clause =
    let trivial = ref false in
    let duplicates = ref [] in
    let res = ref [] in
    Array.iter
      (fun a ->
        if Atom.seen a then duplicates := a :: !duplicates
        else (
          Atom.mark a;
          res := a :: !res
        ))
      clause.atoms;
    List.iter
      (fun a ->
         if Var.seen_both a.var then trivial := true;
         Var.clear a.var)
      !res;
    if !trivial then (
      raise Trivial
    ) else if !duplicates = [] then (
      clause
    ) else (
      Clause.make_l !res (History [clause])
    )

  (* Partition literals for new clauses, into:
     - true literals (maybe makes the clause trivial if the lit is proved true at level 0)
     - unassigned literals, yet to be decided
     - false literals (not suitable to watch, those at level 0 can be removed from the clause)

     Clauses that propagated false lits are remembered to reconstruct resolution proofs.
  *)
  let partition atoms : atom list * clause list =
    let rec partition_aux trues unassigned falses history i =
      if i >= Array.length atoms then (
        trues @ unassigned @ falses, history
      ) else (
        let a = atoms.(i) in
        if a.is_true then (
          let l = a.var.v_level in
          if l = 0 then
            raise Trivial (* A var true at level 0 gives a trivially true clause *)
          else
            (a :: trues) @ unassigned @ falses @
            (arr_to_list atoms (i + 1)), history
        ) else if a.neg.is_true then (
          let l = a.var.v_level in
          if l = 0 then (
            match a.var.reason with
            | Some (Bcp cl) ->
              partition_aux trues unassigned falses (cl :: history) (i + 1)
            (* A var false at level 0 can be eliminated from the clause,
               but we need to kepp in mind that we used another clause to simplify it. *)
            | Some Semantic ->
              partition_aux trues unassigned falses history (i + 1)
            (* Semantic propagations at level 0 are, well not easy to deal with,
               this shouldn't really happen actually (because semantic propagations
               at level 0 should come with a proof). *)
            (* TODO: get a proof of the propagation. *)
            | None | Some Decision -> assert false
            (* The var must have a reason, and it cannot be a decision/assumption,
               since its level is 0. *)
          ) else (
            partition_aux trues unassigned (a::falses) history (i + 1)
          )
        ) else (
          partition_aux trues (a::unassigned) falses history (i + 1)
        )
      )
    in
    partition_aux [] [] [] [] 0


  (* Making a decision.
     Before actually creatig a new decision level, we check that
     all propagations have been done and propagated to the theory,
     i.e that the theoriy state indeed takes into account the whole
     stack of literals
     i.e we have indeed reached a propagation fixpoint before making
     a new decision *)
  let new_decision_level st =
    assert (st.th_head = Vec.size st.trail);
    assert (st.elt_head = Vec.size st.trail);
    Vec.push st.elt_levels (Vec.size st.trail);
    Vec.push st.backtrack_levels (Vec.size st.backtrack); (* save the current theory state *)
    ()

  (* Attach a clause.
     A clause is attached (to its watching lits) when it is first added,
     either because it is assumed or learnt.
  *)
  let attach_clause (self:t) (c:clause) : unit =
    if not (Clause.attached c) then (
      Log.debugf 5 (fun k -> k "(@[sat.attach_clause@ %a@])" Clause.debug c);
      if not (at_level_0 self) then (
        on_backtrack self
          (fun () ->
             Clause.set_attached c false)
      );
      Vec.push c.atoms.(0).neg.watched c;
      Vec.push c.atoms.(1).neg.watched c;
      Clause.set_attached c true;
    )

  (* perform all backtracking actions down to level [l].
     To be called only from [cancel_until] *)
  let backtrack_down_to (st:t) (lvl:int): unit =
    Log.debugf 2 (fun k->k "(@[@{<Yellow>sat.backtrack@} now at level %d@])" lvl);
    while Vec.size st.backtrack > lvl do
      let f = Vec.pop_last st.backtrack in
      f()
    done;
    (* now re-do permanent actions that were backtracked *)
    while not (Vec.is_empty st.to_redo_after_backtrack) do
      let f = Vec.pop_last st.to_redo_after_backtrack in
      f()
    done;
    ()

  (* Backtracking.
     Used to backtrack, i.e cancel down to [lvl] excluded,
     i.e we want to go back to the state the solver was in
         when decision level [lvl] was created. *)
  let cancel_until st lvl =
    Log.debugf 5 (fun k -> k "(@[@{<yellow>sat.cancel_until@}@ :level %d@])" lvl);
    assert (lvl >= base_level st);
    (* Nothing to do if we try to backtrack to a non-existent level. *)
    if decision_level st <= lvl then (
    ) else (
      (* We set the head of the solver and theory queue to what it was. *)
      let head = ref (Vec.get st.elt_levels lvl) in
      st.elt_head <- !head;
      st.th_head <- !head;
      (* Now we need to cleanup the vars that are not valid anymore
         (i.e to the right of elt_head in the queue. *)
      for c = st.elt_head to Vec.size st.trail - 1 do
        let a = Vec.get st.trail c in
        (* A literal is unassigned, we nedd to add it back to
           the heap of potentially assignable literals, unless it has
           a level lower than [lvl], in which case we just move it back. *)
        if a.var.v_level <= lvl then (
          (* It is a late propagation, which has a level
             lower than where we backtrack, so we just move it to the head
             of the queue, to be propagated again. *)
          Vec.set st.trail !head a;
          head := !head + 1
        ) else (
          (* it is a result of bolean propagation, or a semantic propagation
             with a level higher than the level to which we backtrack,
             in that case, we simply unset its value and reinsert it into the heap. *)
          a.is_true <- false;
          a.neg.is_true <- false;
          a.var.v_level <- -1;
          a.var.reason <- None;
          insert_var_order st a.var
        )
      done;
      (* Recover the right theory state. *)
      backtrack_down_to st (Vec.get st.backtrack_levels lvl);
      (* Resize the vectors according to their new size. *)
      Vec.shrink st.trail !head;
      Vec.shrink st.elt_levels lvl;
      Vec.shrink st.backtrack_levels lvl;
    );
    assert (Vec.size st.elt_levels = Vec.size st.backtrack_levels);
    ()

  (* Unsatisfiability is signaled through an exception, since it can happen
     in multiple places (adding new clauses, or solving for instance). *)
  let report_unsat st confl : _ =
    Log.debugf 3 (fun k -> k "(@[sat.unsat_conflict@ %a@])" Clause.debug confl);
    st.unsat_conflict <- Some confl;
    raise Unsat

  (* Simplification of boolean propagation reasons.
     When doing boolean propagation *at level 0*, it can happen
     that the clause cl, which propagates a formula, also contains
     other formulas, but has been simplified. in which case, we
     need to rebuild a clause with correct history, in order to
     be able to build a correct proof at the end of proof search. *)
  let simpl_reason : reason -> reason = function
    | (Bcp cl) as r ->
      let l, history = partition cl.atoms in
      begin match l with
        | [_] ->
          if history = [] then (
            (* no simplification has been done, so [cl] is actually a clause with only
               [a], so it is a valid reason for propagating [a]. *)
            r
          ) else (
            (* Clauses in [history] have been used to simplify [cl] into a clause [tmp_cl]
               with only one formula (which is [a]). So we explicitly create that clause
               and set it as the cause for the propagation of [a], that way we can
               rebuild the whole resolution tree when we want to prove [a]. *)
            let c' = Clause.make_l l (History (cl :: history)) in
            Log.debugf 5
              (fun k -> k "Simplified reason: @[<v>%a@,%a@]" Clause.debug cl Clause.debug c');
            Bcp c'
          )
        | _ ->
          Log.debugf 1
            (fun k ->
               k "@[<v 2>Failed at reason simplification:@,%a@,%a@]"
                 (Vec.print ~sep:"" Atom.debug)
                 (Vec.from_list l Atom.dummy)
                 Clause.debug cl);
          assert false
      end
    | r -> r

  (* Boolean propagation.
     Wrapper function for adding a new propagated formula. *)
  let enqueue_bool st a reason : unit =
    if a.neg.is_true then (
      Util.errorf "(@[sat.enqueue_bool@ :false-literal %a@])" Atom.debug a
    );
    let level = Vec.size st.trail in
    Log.debugf 5
      (fun k->k "(@[sat.enqueue_bool@ :lvl %d@ %a@])" level Atom.debug a);
    let reason = if at_level_0 st then simpl_reason reason else reason in
    (* backtrack assignment if needed. Trail is backtracked automatically. *)
    assert (not a.is_true && a.var.v_level < 0 && a.var.reason = None);
    on_backtrack_if_not_at_0 st
      (fun () ->
         a.var.v_level <- -1;
         a.is_true <- false;
         a.var.reason <- None);
    a.is_true <- true;
    a.var.v_level <- level;
    a.var.reason <- Some reason;
    Vec.push st.trail a;
    ()

  (* swap elements of array *)
  let[@inline] swap_arr a i j =
    if i<>j then (
      let tmp = a.(i) in
      a.(i) <- a.(j);
      a.(j) <- tmp;
    )

  (* move atoms assigned at high levels first *)
  let put_high_level_atoms_first (arr:atom array) : unit =
    Array.iteri
      (fun i a ->
         if i>0 && Atom.level a > Atom.level arr.(0) then (
           (* move first to second, [i]-th to first, second to [i] *)
           if i=1 then (
             swap_arr arr 0 1;
           ) else (
             let tmp = arr.(1) in
             arr.(1) <- arr.(0);
             arr.(0) <- arr.(i);
             arr.(i) <- tmp;
           );
         ) else if i>1 && Atom.level a > Atom.level arr.(1) then (
           swap_arr arr 1 i;
         ))
      arr

  (* find which level to backtrack to, given a conflict clause
     and a boolean stating whether it is
     a UIP ("Unique Implication Point")
     precond: the atom list is sorted by decreasing decision level *)
  let backtrack_lvl st : atom list -> int * bool = function
    | [] | [_] ->
      0, true
    | a :: b :: _ ->
      assert(a.var.v_level > base_level st);
      if a.var.v_level > b.var.v_level then (
        (* backtrack below [a], so we can propagate [not a] *)
        b.var.v_level, true
      ) else (
        assert (a.var.v_level = b.var.v_level);
        assert (a.var.v_level >= base_level st);
        max (a.var.v_level - 1) (base_level st), false
      )

  (* result of conflict analysis, containing the learnt clause and some
     additional info.

     invariant: cr_history's order matters, as its head is later used
     during pop operations to determine the origin of a clause/conflict
     (boolean conflict i.e hypothesis, or theory lemma) *)
  type conflict_res = {
    cr_backtrack_lvl : int; (* level to backtrack to *)
    cr_learnt: atom list; (* lemma learnt from conflict *)
    cr_history: clause list; (* justification *)
    cr_is_uip: bool; (* conflict is UIP? *)
  }

  let[@inline] get_atom st i = Vec.get st.trail i

  (* conflict analysis for SAT
     Same idea as the mcsat analyze function (without semantic propagations),
     except we look the the Last UIP (TODO: check ?), and do it in an imperative
     and efficient manner. *)
  let analyze_sat st c_clause : conflict_res =
    let pathC  = ref 0 in
    let learnt = ref [] in
    let cond   = ref true in
    let blevel = ref 0 in
    let seen   = ref [] in
    let c      = ref (Some c_clause) in
    let tr_ind = ref (Vec.size st.trail - 1) in
    let history = ref [] in
    assert (decision_level st > 0);
    let conflict_level =
      Array.fold_left (fun acc p -> max acc p.var.v_level) 0 c_clause.atoms
    in
    Log.debugf 5
      (fun k -> k "Analyzing conflict (%d): %a" conflict_level Clause.debug c_clause);
    while !cond do
      begin match !c with
        | None ->
          Log.debug 5 "  skipping resolution for semantic propagation"
        | Some clause ->
          Log.debugf 5 (fun k->k"  Resolving clause: %a"  Clause.debug clause);
          begin match clause.cpremise with
            | History _ -> clause_bump_activity st clause
            | Hyp | Local | Lemma _ -> ()
          end;
          history := clause :: !history;
          (* visit the current predecessors *)
          for j = 0 to Array.length clause.atoms - 1 do
            let q = clause.atoms.(j) in
            assert (q.is_true || q.neg.is_true && q.var.v_level >= 0); (* unsure? *)
            if q.var.v_level <= 0 then (
              assert (q.neg.is_true);
              match q.var.reason with
              | Some Bcp cl -> history := cl :: !history
              | _ -> assert false
            );
            if not (Var.seen_both q.var) then (
              Atom.mark q;
              Atom.mark q.neg;
              seen := q :: !seen;
              if q.var.v_level > 0 then (
                var_bump_activity st q.var;
                if q.var.v_level >= conflict_level then (
                  incr pathC;
                ) else (
                  learnt := q :: !learnt;
                  blevel := max !blevel q.var.v_level
                )
              )
            )
          done
      end;

      (* look for the next node to expand *)
      while
        let a = Vec.get st.trail !tr_ind in
        Log.debugf 5 (fun k -> k "  looking at: %a" St.Atom.debug a);
        (not (Var.seen_both a.var)) || (a.var.v_level < conflict_level)
      do
        decr tr_ind;
      done;
      let p = get_atom st !tr_ind in
      decr pathC;
      decr tr_ind;
      match !pathC, p.var.reason with
      | 0, _ ->
        cond := false;
        learnt := p.neg :: (List.rev !learnt)
      | n, Some Semantic ->
        assert (n > 0);
        learnt := p.neg :: !learnt;
        c := None
      | n, Some Bcp cl ->
        assert (n > 0);
        assert (p.var.v_level >= conflict_level);
        c := Some cl
      | _ -> assert false
    done;
    List.iter (fun q -> Var.clear q.var) !seen;
    let l = List.fast_sort (fun p q -> compare q.var.v_level p.var.v_level) !learnt in
    let level, is_uip = backtrack_lvl st l in
    { cr_backtrack_lvl = level;
      cr_learnt = l;
      cr_history = List.rev !history;
      cr_is_uip = is_uip;
    }

  let[@inline] analyze st c_clause : conflict_res =
    analyze_sat st c_clause

  (* add the learnt clause to the clause database, propagate, etc. *)
  let record_learnt_clause st (confl:clause) (cr:conflict_res): unit =
    begin match cr.cr_learnt with
      | [] -> assert false
      | [fuip] ->
        assert (cr.cr_backtrack_lvl = 0);
        if fuip.neg.is_true then (
          report_unsat st confl
        ) else (
          let uclause = Clause.make_l cr.cr_learnt (History cr.cr_history) in
          Vec.push st.clauses_learnt uclause;
          (* no need to attach [uclause], it is true at level 0 *)
          enqueue_bool st fuip (Bcp uclause)
        )
      | fuip :: _ ->
        let lclause = Clause.make_l cr.cr_learnt (History cr.cr_history) in
        Vec.push st.clauses_learnt lclause;
        attach_clause st lclause;
        clause_bump_activity st lclause;
        if cr.cr_is_uip then (
          enqueue_bool st fuip (Bcp lclause)
        ) else (
          st.next_decision <- Some fuip.neg
        )
    end;
    var_decay_activity st;
    clause_decay_activity st

  (* process a conflict:
     - learn clause
     - backtrack
     - report unsat if conflict at level 0
  *)
  let add_boolean_conflict st (confl:clause): unit =
    Log.debugf 3 (fun k -> k "(@[@{<Yellow>boolean conflict@}@ %a@])" Clause.debug confl);
    st.next_decision <- None;
    assert (decision_level st >= base_level st);
    if decision_level st = base_level st ||
       Array.for_all (fun a -> a.var.v_level <= base_level st) confl.atoms then (
      (* Top-level conflict *)
      report_unsat st confl;
    );
    let cr = analyze st confl in
    cancel_until st (max cr.cr_backtrack_lvl (base_level st));
    record_learnt_clause st confl cr

  (* Get the correct vector to insert a clause in. *)
  let rec clause_vector st c =
    match c.cpremise with
    | Hyp -> st.clauses_hyps
    | Local -> st.clauses_temp
    | History [c'] -> clause_vector st c' (* simplified version of [d] *)
    | Lemma _ | History _ -> st.clauses_learnt

  (* TODO: rewrite this, accounting for backtracking semantics.
   - if clause is already true, probably just do nothing
   - if clause is unit, propagate lit immediately (with clause as justification)
     but do not add clause

   TODO: also, remove buffering of clauses to add
   *)

  (* add permanent clause, to be kept down to level 0.
     precond: non empty clause
     @param atoms list of atoms of [c]
     @param c the clause itself *)
  let add_clause_permanent st (atoms:atom list) (clause:clause) : unit =
    Log.debugf 5 (fun k->k "(@[sat.add_clause_permanent@ %a@])" Clause.debug clause);
    let vec_for_clause = clause_vector st clause in
    match atoms with
    | [] -> assert false
    | [a]   ->
      if a.neg.is_true then (
        (* Since we cannot propagate the atom [a], in order to not lose
           the information that [a] must be true, we add clause to the list
           of clauses to add, so that it will be e-examined later. *)
        Log.debug 5 "Unit clause, report failure";
        report_unsat st clause
      ) else if a.is_true then (
        (* If the atom is already true, then it should be because of a local hyp.
           However it means we can't propagate it at level 0. In order to not lose
           that information, we store the clause in a stack of clauses that we will
           add to the solver at the next pop. *)
        Log.debug 5 "Unit clause, adding to root clauses";
        assert (0 < a.var.v_level && a.var.v_level <= base_level st);
        on_backtrack_if_not_at_0 st (fun () -> Vec.pop vec_for_clause);
        Vec.push vec_for_clause clause;
      ) else (
        Log.debugf 5
          (fun k->k "(@[sat.add_clause.unit-clause@ :propagating %a@])" Atom.debug a);
        on_backtrack_if_not_at_0 st (fun () -> Vec.pop vec_for_clause);
        Vec.push vec_for_clause clause;
        enqueue_bool st a (Bcp clause)
      )
    | a::b::_ ->
      Vec.push vec_for_clause clause;
      if a.neg.is_true then (
        (* Atoms need to be sorted in decreasing order of decision level,
           or we might watch the wrong literals. *)
        put_high_level_atoms_first clause.atoms;
        attach_clause st clause;
        add_boolean_conflict st clause
      ) else (
        attach_clause st clause;
        if b.neg.is_true && not a.is_true && not a.neg.is_true then (
          let lvl = List.fold_left (fun m a -> max m a.var.v_level) 0 atoms in
          cancel_until st (max lvl (base_level st));
          enqueue_bool st a (Bcp clause)
        )
      )

  (* Add a new clause, simplifying, propagating, and backtracking if
     the clause is false in the current trail *)
  let add_clause ~permanent st (init:clause) : unit =
    Log.debugf 5
      (fun k -> k "(@[@{<Yellow>sat.add_clause@}@ :permanent %B@ %a@])"
          permanent Clause.debug init);
    let vec_for_clause = clause_vector st init in
    match eliminate_duplicates init with
    | c ->
      Log.debugf 5 (fun k -> k "(@[sat.add_clause.after_eliminate_dups@ %a@])" Clause.debug c);
      let atoms, history = partition c.atoms in
      let clause =
        if history = []
        then (
          (* update order of atoms *)
          List.iteri (fun i a -> c.atoms.(i) <- a) atoms;
          c
        ) else (
          Clause.make_l atoms (History (c :: history))
        )
      in
      Log.debugf 3 (fun k->k "(@[sat.add_clause.new_clause@ %a@])" Clause.debug clause);
      match atoms with
      | [] ->
        (* report Unsat immediately *)
        report_unsat st clause
      | _::_ when permanent ->
        (* add clause, down to level 0 *)
        redo_down_to_level_0 st
          (fun () -> add_clause_permanent st atoms clause)
      | [a] ->
        if a.neg.is_true then (
          (* Since we cannot propagate the atom [a], in order to not lose
             the information that [a] must be true, we add clause to the list
             of clauses to add, so that it will be e-examined later. *)
          Log.debug 5 "(sat.add_clause: false unit clause, report unsat)";
          report_unsat st clause
        ) else if a.is_true then (
          (* If the atom is already true, then it should be because of a local hyp.
             However it means we can't propagate it at level 0. In order to not lose
             that information, we store the clause in a stack of clauses that we will
             add to the solver at the next pop. *)
          Log.debug 5 "(sat.add_clause: true unit clause, ignore)";
          assert (0 < a.var.v_level && a.var.v_level <= base_level st);
        ) else (
          Log.debugf 5
            (fun k->k "(@[sat.add_clause.unit-clause@ :propagating %a@])" Atom.debug a);
          (* propagate but without adding the clause. May need to
             re-propagate after backtracking *)
          redo_down_to_level_0 st
            (fun () -> enqueue_bool st a (Bcp clause))
        )
      | a::b::_ ->
        on_backtrack_if_not_at_0 st (fun () -> Vec.pop vec_for_clause);
        Vec.push vec_for_clause clause;
        if a.neg.is_true then (
          (* Atoms need to be sorted in decreasing order of decision level,
             or we might watch the wrong literals. *)
          put_high_level_atoms_first clause.atoms;
          attach_clause st clause;
          add_boolean_conflict st clause
        ) else (
          attach_clause st clause;
          if b.neg.is_true && not a.is_true && not a.neg.is_true then (
            let lvl = List.fold_left (fun m a -> max m a.var.v_level) 0 atoms in
            cancel_until st (max lvl (base_level st));
            enqueue_bool st a (Bcp clause)
          )
        )
    | exception Trivial ->
      Vec.push vec_for_clause init;
      Log.debugf 3 (fun k->k "(@[sat.add_clause.ignore-trivial@ %a@])" Clause.debug init)

  type watch_res =
    | Watch_kept
    | Watch_removed

  exception Exn_remove_watch

  (* boolean propagation.
     [a] is the false atom, one of [c]'s two watch literals
     [i] is the index of [c] in [a.watched]
     @return whether [c] was removed from [a.watched]
  *)
  let propagate_in_clause st (a:atom) (c:clause) : watch_res =
    let atoms = c.atoms in
    let first = atoms.(0) in
    if first == a.neg then (
      (* false lit must be at index 1 *)
      atoms.(0) <- atoms.(1);
      atoms.(1) <- first
    ) else (
      assert (a.neg == atoms.(1));
    );
    let first = atoms.(0) in
    if first.is_true
    then Watch_kept (* true clause, keep it in watched *)
    else (
      try (* look for another watch lit *)
        for k = 2 to Array.length atoms - 1 do
          let ak = atoms.(k) in
          if not (ak.neg.is_true) then (
            (* watch lit found: update and exit *)
            Array.unsafe_set atoms 1 ak;
            Array.unsafe_set atoms k a.neg;
            (* remove [c] from [a.watched], add it to [ak.neg.watched] *)
            Vec.push ak.neg.watched c;
            raise Exn_remove_watch
          )
        done;
        (* no watch lit found *)
        if first.neg.is_true then (
          (* clause is false *)
          st.elt_head <- Vec.size st.trail;
          raise (Conflict c)
        ) else (
          enqueue_bool st first (Bcp c)
        );
        Watch_kept
      with Exn_remove_watch ->
        Watch_removed
    )

  (* propagate atom [a], which was just decided. This checks every
     clause watching [a] to see if the clause is false, unit, or has
     other possible watches
     @param res the optional conflict clause that the propagation might trigger *)
  let propagate_atom st a : unit =
    let watched = a.watched in
    let i = ref 0 in
    while !i < Vec.size watched do
      let c = Vec.get watched !i in
      assert (Clause.attached c);
      if not (Clause.attached c) then (
        Vec.fast_remove watched !i (* remove *)
      ) else (
        match propagate_in_clause st a c with
        | Watch_kept -> incr i
        | Watch_removed ->
          Vec.fast_remove watched !i;
          (* remove clause [c] from watches, then look again at [!i]
             since it's now another clause *)
      )
    done

  let slice_iter st (f:_ -> unit) : unit =
    let n = Vec.size st.trail in
    for i = st.th_head to n-1 do
      let a = Vec.get st.trail i in
      f a.lit
    done

  let act_push_ ~permanent st (l:formula IArray.t) (lemma:proof): unit =
    let atoms = IArray.to_array_map (mk_atom st) l in
    let c = Clause.make atoms (Lemma lemma) in
    Log.debugf 3 (fun k->k "(@[sat.push_clause@ %a@])" Clause.debug c);
    add_clause ~permanent st c

  (* TODO: ensure that the clause is removed upon backtracking *)
  let act_push_local = act_push_ ~permanent:false
  let act_push_persistent = act_push_ ~permanent:true

  (* TODO: ensure that the clause is removed upon backtracking *)
  let act_propagate (st:t) f causes proof : unit =
    let l = List.rev_map (mk_atom st) causes in
    if List.for_all (fun a -> a.is_true) l then (
      let p = mk_atom st f in
      let c = Clause.make_l (p :: List.map Atom.neg l) (Lemma proof) in
      if p.is_true then (
      ) else if p.neg.is_true then (
        add_clause ~permanent:false st c
      ) else (
        insert_var_order st p.var;
        enqueue_bool st p (Bcp c)
      )
    ) else (
      Util.errorf "(@[sat.act_propagate.invalid_guard@ :guard %a@ \
                   :error all lits are not true@])"
        (Util.pp_list Atom.debug) l
    )

  let current_slice st = Theory_intf.Slice_acts {
    slice_iter = slice_iter st;
  }

  (* full slice, for [if_sat] final check *)
  let full_slice st = Theory_intf.Slice_acts {
    slice_iter = slice_iter st;
  }

  let act_at_level_0 st () = at_level_0 st

  let actions st = Theory_intf.Actions {
    push_persistent = act_push_persistent st;
    push_local = act_push_local st;
    on_backtrack = on_backtrack st;
    at_level_0 = act_at_level_0 st;
    propagate = act_propagate st;
  }

  let create ?(size=`Big) ?st () : t =
    let st = match st with Some s -> s | None -> St.create ~size () in
    let size_trail, size_lvl = match size with
      | `Tiny -> 0, 0
      | `Small -> 32, 16
      | `Big -> 600, 50
    in
    let rec solver = lazy (
      create_ ~st ~size_trail ~size_lvl th
    ) and th = lazy (
      Th.create (actions (Lazy.force solver))
    ) in
    Lazy.force solver

  let[@inline] propagation_fixpoint (st:t) : bool =
    st.elt_head = Vec.size st.trail &&
    st.th_head = st.elt_head

  (* some boolean literals were decided/propagated within the solver. Now we
     need to inform the theory of those assumptions, so it can do its job.
     @return the conflict clause, if the theory detects unsatisfiability *)
  let rec theory_propagate st : clause option =
    assert (st.elt_head = Vec.size st.trail);
    assert (st.th_head <= st.elt_head);
    if st.th_head = st.elt_head then (
      None (* fixpoint/no propagation *)
    ) else (
      let slice = current_slice st in
      st.th_head <- st.elt_head; (* catch up *)
      match Th.assume (theory st) slice with
      | Theory_intf.Sat ->
        propagate st
      | Theory_intf.Unsat (l, p) ->
        (* conflict *)
        let l = List.rev_map (mk_atom st) l in
        List.iter (fun a -> insert_var_order st a.var) l;
        let c = St.Clause.make_l l (Lemma p) in
        Some c
    )

  (* fixpoint between boolean propagation and theory propagation
     @return a conflict clause, if any *)
  and propagate (st:t) : clause option =
    (* Now, check that the situation is sane *)
    assert (st.elt_head <= Vec.size st.trail);
    if st.elt_head = Vec.size st.trail then
      theory_propagate st
    else (
      let num_props = ref 0 in
      let res = ref None in
      while st.elt_head < Vec.size st.trail do
        let a = Vec.get st.trail st.elt_head in
        incr num_props;
        propagate_atom st a;
        st.elt_head <- st.elt_head + 1;
      done;
      match !res with
      | None -> theory_propagate st
      | _ -> !res
    )

  (* remove some learnt clauses
     NOTE: so far we do not forget learnt clauses. We could, as long as
     lemmas from the theory itself are kept. *)
  let reduce_db () = ()

  (* Decide on a new literal, and enqueue it into the trail *)
  let rec pick_branch_aux st atom : unit =
    let v = atom.var in
    if v.v_level >= 0 then (
      assert (v.pa.is_true || v.na.is_true);
      pick_branch_lit st
    ) else (
      new_decision_level st;
      enqueue_bool st atom Decision
    )

  and pick_branch_lit st =
    match st.next_decision with
    | Some atom ->
      st.next_decision <- None;
      pick_branch_aux st atom
    | None ->
      begin match H.remove_min st.order with
        | v -> pick_branch_aux st v.pa
        | exception Not_found -> raise Sat
      end

  (* do some amount of search, until the number of conflicts or clause learnt
     reaches the given parameters *)
  let search (st:t) n_of_conflicts n_of_learnts : unit =
    let conflictC = ref 0 in
    while true do
      match propagate st with
      | Some confl -> (* Conflict *)
        incr conflictC;
        add_boolean_conflict st confl

      | None -> (* No Conflict *)
        assert (st.elt_head = Vec.size st.trail);
        assert (st.elt_head = st.th_head);
        if Vec.size st.trail = St.nb_elt st.st
        then raise Sat;
        if n_of_conflicts > 0 && !conflictC >= n_of_conflicts then (
          Log.debug 3 "Restarting...";
          cancel_until st (base_level st);
          raise Restart
        );
        (* if decision_level() = 0 then simplify (); *)

        if n_of_learnts >= 0 &&
           Vec.size st.clauses_learnt - Vec.size st.trail >= n_of_learnts
        then reduce_db();

        pick_branch_lit st
    done

  let eval_level (st:t) lit =
    let var, negated = Var.make st.st lit in
    if not var.pa.is_true && not var.na.is_true
    then raise UndecidedLit
    else assert (var.v_level >= 0);
    let truth = var.pa.is_true in
    let value = match negated with
      | Theory_intf.Negated -> not truth
      | Theory_intf.Same_sign -> truth
    in
    value, var.v_level

  let eval st lit = fst (eval_level st lit)

  let[@inline] unsat_conflict st = st.unsat_conflict

  (* fixpoint of propagation and decisions until a model is found, or a
     conflict is reached *)
  let solve (st:t) : unit =
    Log.debug 5 "solve";
    if is_unsat st then raise Unsat;
    let n_of_conflicts = ref (to_float restart_first) in
    let n_of_learnts = ref ((to_float (nb_clauses st)) *. learntsize_factor) in
    try
      while true do
        begin
          try
            search st (to_int !n_of_conflicts) (to_int !n_of_learnts)
          with
          | Restart ->
            n_of_conflicts := !n_of_conflicts *. restart_inc;
            n_of_learnts   := !n_of_learnts *. learntsize_inc
          | Sat ->
            assert (st.elt_head = Vec.size st.trail);
            begin match Th.if_sat (theory st) (full_slice st) with
              | Theory_intf.Sat ->
                (* if no propagation is to be done, exit;
                   otherwise continue loop *)
                if propagation_fixpoint st then (
                  raise Sat
                )
              | Theory_intf.Unsat (l, p) ->
                let atoms = List.rev_map (mk_atom st) l in
                let c = Clause.make_l atoms (Lemma p) in
                Log.debugf 3
                  (fun k -> k "(@[@{<Yellow>sat.theory_conflict_clause@}@ %a@])" Clause.debug c);
                (* must backtrack *)
                (* TODO: assert that this is indeed a conflict,
                   then call [add_boolean_conflict st c] *)
                add_clause ~permanent:false st c
            end;
        end
      done
    with Sat -> ()

  let assume ~permanent st ?tag cnf =
    let cs = List.rev_map
      (fun atoms ->
         let atoms = List.rev_map (mk_atom st) atoms in
         Clause.make_l ?tag atoms Hyp)
      cnf
    in
    let add_clauses () =
      List.iter
        (fun c ->
           Log.debugf 5 (fun k -> k "(@[sat.assume@ %a@])" Clause.debug c);
           add_clause ~permanent:false st c)
        cs
    in
  if permanent
    then redo_down_to_level_0 st add_clauses
    else add_clauses()

  (* create a factice decision level for local assumptions *)
  let push st : unit =
    Log.debug 5 "Pushing a new user level";
    cancel_until st (base_level st);
    Log.debugf 5
      (fun k -> k "@[<v>Status:@,@[<hov 2>trail: %d - %d@,%a@]"
          st.elt_head st.th_head (Vec.print ~sep:"" Atom.debug) st.trail);
    begin match propagate st with
      | Some confl ->
        report_unsat st confl
      | None ->
        Log.debugf 5
          (fun k -> k "@[<v>Current trail:@,@[<hov>%a@]@]"
              (Vec.print ~sep:"" Atom.debug) st.trail);
        Log.debug 3 "Creating new user level";
        new_decision_level st;
        Vec.push st.user_levels (Vec.size st.clauses_temp);
        assert (decision_level st = base_level st)
    end

  (* pop the last factice decision level *)
  let pop st : unit =
    if base_level st = 0 then (
      Log.debug 2 "(sat.error: cannot pop (already at level 0))"
    ) else (
      Log.debug 3 "(sat.pop-user-level)";
      assert (base_level st > 0);
      st.unsat_conflict <- None;
      let n = Vec.last st.user_levels in
      Vec.pop st.user_levels; (* before the [cancel_until]! *)
      (* remove from env.clauses_temp the now invalid caluses. *)
      Vec.shrink st.clauses_temp n;
      assert (Vec.for_all (fun c -> Array.length c.atoms = 1) st.clauses_temp);
      assert (Vec.for_all (fun c -> c.atoms.(0).var.v_level <= base_level st) st.clauses_temp);
      cancel_until st (base_level st)
    )

  (* Add local hyps to the current decision level *)
  let local (st:t) (assumptions:formula list) : unit =
    let add_lit lit : unit =
      let a = mk_atom st lit in
      Log.debugf 3 (fun k-> k "(@[sat.local_assumption@ %a@])" Atom.debug a);
      assert (decision_level st = base_level st);
      if not a.is_true then (
        let c = Clause.make [|a|] Local in
        Log.debugf 5 (fun k -> k "(@[sat.add_temp_clause@ %a@])" Clause.debug c);
        Vec.push st.clauses_temp c;
        if a.neg.is_true then (
          (* conflict between assumptions: UNSAT *)
          report_unsat st c;
        ) else (
          (* make a decision, propagate *)
          enqueue_bool st a (Bcp c);
        )
      )
    in
    assert (base_level st > 0);
    match st.unsat_conflict with
    | None ->
      Log.debug 3 "(sat.adding_local_assumptions)";
      cancel_until st (base_level st);
      List.iter add_lit assumptions
    | Some _ ->
      Log.debug 2 "(sat.local_assumptions.error: already unsat)"

  (* Check satisfiability *)
  let check_clause c =
    let tmp = Array.map (fun a ->
        if a.is_true then true
        else if a.neg.is_true then false
        else raise UndecidedLit) c.atoms in
    let res = Array.exists (fun x -> x) tmp in
    if not res then (
      Log.debugf 5
        (fun k -> k "Clause not satisfied: @[<hov>%a@]" Clause.debug c);
      false
    ) else
      true

  let check_vec v =
    Vec.for_all check_clause v

  let check_stack s =
    try
      Stack.iter (fun c -> if not (check_clause c) then raise Exit) s;
      true
    with Exit ->
      false

  let check st : bool =
    check_vec st.clauses_hyps &&
    check_vec st.clauses_learnt &&
    check_vec st.clauses_temp

  (* Unsafe access to internal data *)

  let hyps env = env.clauses_hyps

  let history env = env.clauses_learnt

  let temp env = env.clauses_temp

  let trail env = env.trail

end
[@@inline]

