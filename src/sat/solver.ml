open Sidekick_core
open Sigs
open Base_types_

let invalid_argf fmt =
  Format.kasprintf (fun msg -> invalid_arg ("sidekick.sat: " ^ msg)) fmt

type clause = Clause0.t
type store = Store.t
type plugin = Sigs.plugin

module Atom = Store.Atom
module Var = Store.Var
module Clause = Store.Clause

module H = Heap.Make [@specialise] (struct
  type store = Store.t
  type t = var

  let[@inline] cmp store i j = Var.weight store j < Var.weight store i
  (* comparison by weight *)

  let heap_idx = Var.heap_idx
  let set_heap_idx = Var.set_heap_idx
  let of_int_unsafe = Var.of_int_unsafe
end)

(* cause of "unsat", possibly conditional to local assumptions *)
type unsat_cause =
  | US_local of {
      first: atom; (* assumption which was found to be proved false *)
      core: atom list; (* the set of assumptions *)
    }
  | US_false of clause
(* true unsat *)

exception E_sat
exception E_unsat of unsat_cause
exception UndecidedLit
exception Restart
exception Conflict of clause

let var_decay : float = 1. /. 0.95
(* inverse of the activity factor for variables *)

let clause_decay : float = 1. /. 0.999
(* inverse of the activity factor for clauses *)

let restart_inc : float = 1.5
(* multiplicative factor for restart limit *)

let learntsize_inc : float = 1.1
(* multiplicative factor for [learntsize_factor] at each restart *)

(** Passed to clause pools when it's time to garbage collect clauses *)
module type GC_ARG = sig
  val store : Store.t
  val must_keep_clause : clause -> bool
  val flag_clause_for_gc : clause -> unit
end

(** A clause pool *)
module type CLAUSE_POOL = sig
  val add : clause -> unit
  val descr : unit -> string
  val gc : (module GC_ARG) -> unit
  val iter : f:(clause -> unit) -> unit
  val needs_gc : unit -> bool
  val size : unit -> int
end

(* a clause pool *)
type clause_pool = (module CLAUSE_POOL)

(* a pool with garbage collection determined by [P] *)
module Make_gc_cp (P : sig
  val descr : unit -> string
  val max_size : int ref
end)
() : CLAUSE_POOL = struct
  let clauses_ : clause Vec.t = Vec.create ()
  (* Use a [Vec] so we can sort it.
     TODO: when we can sort any vec, come back to that. *)

  let descr = P.descr
  let add c = Vec.push clauses_ c
  let iter ~f = Vec.iter ~f clauses_
  let size () = Vec.size clauses_
  let needs_gc () = size () > !P.max_size

  let gc (module G : GC_ARG) : unit =
    (* find clauses to GC *)
    let to_be_pushed_back = CVec.create () in

    (* sort by decreasing activity *)
    Vec.sort clauses_ (fun c1 c2 ->
        compare (Clause.activity G.store c2) (Clause.activity G.store c1));

    while Vec.size clauses_ > !P.max_size do
      let c = Vec.pop_exn clauses_ in
      if G.must_keep_clause c then
        CVec.push to_be_pushed_back c
      (* must keep it, it's on the trail *)
      else
        G.flag_clause_for_gc c
    done;
    (* transfer back clauses we had to keep *)
    CVec.iter ~f:(Vec.push clauses_) to_be_pushed_back;
    ()
end

let make_gc_clause_pool_ ~descr ~max_size () : clause_pool =
  (module Make_gc_cp
            (struct
              let descr = descr
              let max_size = max_size
            end)
            ())

let[@inline] cp_size_ (module P : CLAUSE_POOL) : int = P.size ()
let[@inline] cp_needs_gc_ (module P : CLAUSE_POOL) : bool = P.needs_gc ()
let[@inline] cp_add_ (module P : CLAUSE_POOL) c : unit = P.add c
let[@inline] cp_to_iter_ (module P : CLAUSE_POOL) yield : unit = P.iter ~f:yield

(* initial limit for the number of learnt clauses, 1/3 of initial
    number of clauses by default *)
let learntsize_factor = 1. /. 3.

(** Actions from theories and user, but to be done in specific points
      of the solving loops. *)
module Delayed_actions : sig
  type t

  val create : unit -> t
  val is_empty : t -> bool
  val clear_on_backtrack : t -> unit
  val add_clause_learnt : t -> clause -> unit
  val propagate_atom : t -> atom -> lvl:int -> clause lazy_t -> unit
  val add_decision : t -> atom -> unit

  val iter :
    decision:(atom -> unit) ->
    propagate:(atom -> lvl:int -> clause lazy_t -> unit) ->
    add_clause_learnt:(clause -> unit) ->
    add_clause_pool:(clause -> clause_pool -> unit) ->
    t ->
    unit
end = struct
  type t = {
    clauses_to_add_learnt: CVec.t;
    (* Clauses either assumed or pushed by the theory, waiting to be added. *)
    clauses_to_add_in_pool: (clause * clause_pool) Vec.t;
    (* clauses to add into a pool *)
    mutable prop_level: int;
    propagate: (atom * int * clause lazy_t) Vec.t;
    decisions: atom Vec.t;
  }

  let create () : t =
    {
      clauses_to_add_learnt = CVec.create ();
      clauses_to_add_in_pool = Vec.create ();
      prop_level = -1;
      propagate = Vec.create ();
      decisions = Vec.create ();
    }

  let clear self =
    let {
      clauses_to_add_learnt;
      clauses_to_add_in_pool;
      prop_level = _;
      propagate;
      decisions;
    } =
      self
    in
    Vec.clear clauses_to_add_in_pool;
    CVec.clear clauses_to_add_learnt;
    Vec.clear propagate;
    Vec.clear decisions

  let clear_on_backtrack self =
    let {
      clauses_to_add_learnt = _;
      clauses_to_add_in_pool = _;
      propagate;
      prop_level = _;
      decisions;
    } =
      self
    in
    Vec.clear propagate;
    Vec.clear decisions

  let is_empty self =
    let {
      clauses_to_add_learnt;
      clauses_to_add_in_pool;
      prop_level = _;
      propagate;
      decisions;
    } =
      self
    in
    Vec.is_empty clauses_to_add_in_pool
    && CVec.is_empty clauses_to_add_learnt
    && Vec.is_empty decisions && Vec.is_empty propagate

  let add_clause_learnt (self : t) c = CVec.push self.clauses_to_add_learnt c

  let propagate_atom self p ~lvl c =
    if (not (Vec.is_empty self.propagate)) && lvl < self.prop_level then
      Vec.clear self.propagate
    (* will be immediately backtracked *);
    if lvl <= self.prop_level then (
      self.prop_level <- lvl;
      Vec.push self.propagate (p, lvl, c)
    )

  let add_decision self p = Vec.push self.decisions p

  let iter ~decision ~propagate ~add_clause_learnt ~add_clause_pool self : unit
      =
    let {
      clauses_to_add_learnt;
      clauses_to_add_in_pool;
      prop_level = _;
      propagate = prop;
      decisions;
    } =
      self
    in
    Vec.iter clauses_to_add_in_pool ~f:(fun (c, p) -> add_clause_pool c p);
    CVec.iter ~f:add_clause_learnt clauses_to_add_learnt;
    Vec.iter ~f:decision decisions;
    Vec.iter prop ~f:(fun (p, lvl, c) -> propagate p ~lvl c);
    clear self;
    ()
end

(* Singleton type containing the current state *)
type t = {
  store: store; (* atom/var/clause store *)
  plugin: plugin; (* user defined theory *)
  proof: Proof_trace.t; (* the proof object *)
  (* Clauses are simplified for efficiency purposes. In the following
     vectors, the comments actually refer to the original non-simplified
     clause. *)
  clauses_hyps: CVec.t; (* clauses added by the user, never removed *)
  max_clauses_learnt: int ref; (* used to direct GC in {!clauses_learnt} *)
  clauses_learnt: clause_pool;
  (* learnt clauses (tautologies true at any time, whatever the user level).
     GC'd regularly. *)
  clause_pools: clause_pool Vec.t; (* custom clause pools *)
  delayed_actions: Delayed_actions.t;
  mutable unsat_at_0: clause option; (* conflict at level 0, if any *)
  mutable next_decisions: atom list;
  (* When the last conflict was a semantic one (mcsat),
     this stores the next decision to make;
     if some theory wants atoms to be decided on (for theory combination),
     store them here. *)
  trail: AVec.t;
  (* decision stack + propagated elements (atoms or assignments). *)
  var_levels: Veci.t; (* decision levels in [trail]  *)
  assumptions: AVec.t; (* current assumptions *)
  mutable th_head: int;
  (* Start offset in the queue {!trail} of
     unit facts not yet seen by the theory. *)
  mutable elt_head: int;
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
  order: H.t; (* Heap ordered by variable activity *)
  to_clear: var Vec.t; (* variables to unmark *)
  (* temporaries *)
  temp_atom_vec: AVec.t;
  temp_clause_vec: CVec.t;
  temp_step_vec: Step_vec.t;
  mutable var_incr: float; (* increment for variables' activity *)
  mutable clause_incr: float; (* increment for clauses' activity *)
  (* FIXME: use event *)
  on_conflict: (Clause.t, unit) Event.Emitter.t;
  on_decision: (Lit.t, unit) Event.Emitter.t;
  on_learnt: (Clause.t, unit) Event.Emitter.t;
  on_gc: (Lit.t array, unit) Event.Emitter.t;
  stat: Stat.t;
  n_conflicts: int Stat.counter;
  n_propagations: int Stat.counter;
  n_decisions: int Stat.counter;
  n_restarts: int Stat.counter;
  n_minimized_away: int Stat.counter;
}

type solver = t

(* intial restart limit *)
let restart_first = 100
let _nop_on_conflict (_ : atom array) = ()

(* Starting environment. *)
let create_ ~store ~proof ~stat ~max_clauses_learnt (plugin : plugin) : t =
  {
    store;
    plugin;
    unsat_at_0 = None;
    next_decisions = [];
    max_clauses_learnt;
    clauses_hyps = CVec.create ();
    clauses_learnt =
      make_gc_clause_pool_
        ~descr:(fun () -> "cp.learnt-clauses")
        ~max_size:max_clauses_learnt ();
    delayed_actions = Delayed_actions.create ();
    clause_pools = Vec.create ();
    to_clear = Vec.create ();
    temp_clause_vec = CVec.create ();
    temp_atom_vec = AVec.create ();
    temp_step_vec = Step_vec.create ();
    th_head = 0;
    elt_head = 0;
    trail = AVec.create ();
    var_levels = Veci.create ();
    assumptions = AVec.create ();
    order = H.create store;
    var_incr = 1.;
    clause_incr = 1.;
    proof;
    stat;
    n_conflicts = Stat.mk_int stat "sat.n-conflicts";
    n_decisions = Stat.mk_int stat "sat.n-decisions";
    n_propagations = Stat.mk_int stat "sat.n-propagations";
    n_restarts = Stat.mk_int stat "sat.n-restarts";
    n_minimized_away = Stat.mk_int stat "sat.n-confl-lits-minimized-away";
    on_conflict = Event.Emitter.create ();
    on_decision = Event.Emitter.create ();
    on_learnt = Event.Emitter.create ();
    on_gc = Event.Emitter.create ();
  }

let on_gc self = Event.of_emitter self.on_gc
let on_conflict self = Event.of_emitter self.on_conflict
let on_decision self = Event.of_emitter self.on_decision
let on_learnt self = Event.of_emitter self.on_learnt

(* iterate on all learnt clauses, pools included *)
let iter_clauses_learnt_ (self : t) ~f : unit =
  let[@inline] iter_pool (module P : CLAUSE_POOL) = P.iter ~f in
  iter_pool self.clauses_learnt;
  Vec.iter ~f:iter_pool self.clause_pools;
  ()

let[@inline] decision_level st = Veci.size st.var_levels
let[@inline] nb_clauses st = CVec.size st.clauses_hyps
let stat self = self.stat

(* Do we have a level-0 empty clause? *)
let[@inline] check_unsat_ st =
  match st.unsat_at_0 with
  | Some c -> raise (E_unsat (US_false c))
  | None -> ()

(* Variable and literal activity.
   Activity is used to decide on which variable to decide when propagation
   is done. Uses a heap (implemented in Iheap), to keep track of variable activity.
   To be more general, the heap only stores the variable/literal id (i.e an int).
*)
let[@inline] insert_var_order st (v : var) : unit = H.insert st.order v

(* find atom for the lit, if any *)
let[@inline] find_atom_ (self : t) (p : Lit.t) : atom option =
  Store.find_atom self.store p

(* create a new atom, pushing it into the decision queue if needed *)
let make_atom_ (self : t) ?default_pol (p : Lit.t) : atom =
  let a = Store.alloc_atom self.store ?default_pol p in
  if Atom.level self.store a < 0 then
    insert_var_order self (Atom.var a)
  else
    assert (Atom.is_true self.store a || Atom.is_false self.store a);
  a

(* Rather than iterate over all the heap when we want to decrease all the
   variables/literals activity, we instead increase the value by which
   we increase the activity of 'interesting' var/lits. *)
let[@inline] var_decay_activity st = st.var_incr <- st.var_incr *. var_decay

let[@inline] clause_decay_activity st =
  st.clause_incr <- st.clause_incr *. clause_decay

(* increase activity of [v] *)
let var_bump_activity self v =
  let store = self.store in
  Var.set_weight store v (Var.weight store v +. self.var_incr);
  if Var.weight store v > 1e100 then (
    Store.iter_vars store (fun v ->
        Var.set_weight store v (Var.weight store v *. 1e-100));
    self.var_incr <- self.var_incr *. 1e-100
  );
  if H.in_heap self.order v then H.decrease self.order v

(* increase activity of clause [c] *)
let clause_bump_activity self (c : clause) : unit =
  let store = self.store in
  Clause.set_activity store c (Clause.activity store c +. self.clause_incr);
  if Clause.activity store c > 1e20 then (
    let update_clause c =
      Clause.set_activity store c (Clause.activity store c *. 1e-20)
    in
    iter_clauses_learnt_ self ~f:update_clause;
    self.clause_incr <- self.clause_incr *. 1e-20
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

(* get/build the proof for [a], which must be an atom true at level 0.
   This uses a global cache to avoid repeated computations, as many clauses
   might resolve against a given 0-level atom. *)
let rec proof_of_atom_lvl0_ (self : t) (a : atom) : Proof_step.id =
  assert (Atom.is_true self.store a && Atom.level self.store a = 0);

  match Atom.proof_lvl0 self.store a with
  | Some p -> p
  | None ->
    let p =
      match Atom.reason self.store a with
      | None -> assert false
      | Some Decision -> assert false (* no decisions at level0 *)
      | Some (Bcp c2 | Bcp_lazy (lazy c2)) ->
        Log.debugf 50 (fun k ->
            k "(@[sat.proof-of-atom-lvl0.clause@ %a@])"
              (Clause.debug self.store) c2);

        let steps = ref [] in
        (* recurse, so we get the whole level-0 resolution graph *)
        Clause.iter self.store c2 ~f:(fun a2 ->
            if not (Var.equal (Atom.var a) (Atom.var a2)) then (
              Log.debugf 50 (fun k ->
                  k
                    "(@[sat.proof-of-atom-lvl0@ :of %a@ @[:resolve-with@ \
                     %a@]@])"
                    (Atom.debug self.store) a (Atom.debug self.store) a2);

              let p2 = proof_of_atom_lvl0_ self (Atom.neg a2) in
              steps := p2 :: !steps
            ));

        let proof_c2 = Clause.proof_step self.store c2 in
        if !steps = [] then
          proof_c2
        else
          Proof_trace.add_step self.proof @@ fun () ->
          Proof_sat.sat_redundant_clause
            [ Atom.lit self.store a ]
            ~hyps:Iter.(cons proof_c2 (of_list !steps))
    in

    Atom.set_proof_lvl0 self.store a p;
    (* put in cache *)
    p

(* Preprocess clause, by doing the following:

   - Partition literals for new clauses, into:
     - true literals (maybe makes the clause trivial if the lit is proved true at level 0)
     - unassigned literals, yet to be decided
     - false literals (not suitable to watch, those at level 0 can be removed from the clause)
     and order them as such in the result.

   - Also, removes literals that are false at level0, and returns a proof for
     their removal.
   - Also, removes duplicates.
*)
let preprocess_clause_ (self : t) (c : Clause.t) : Clause.t =
  let store = self.store in
  let res0_proofs = ref [] in
  (* steps of resolution at level 0 *)
  let add_proof_lvl0_ p = res0_proofs := p :: !res0_proofs in

  let trues = Vec.create () in
  let unassigned = Vec.create () in
  let falses = Vec.create () in

  (* cleanup marks used to detect duplicates *)
  let cleanup () =
    Clause.iter store c ~f:(fun a -> Store.clear_var store (Atom.var a))
  in

  let consider_atom (a : atom) : unit =
    if not (Atom.marked store a) then (
      Atom.mark store a;
      if Atom.marked_both store a then raise Trivial;

      if Atom.is_true store a then (
        let lvl = Atom.level store a in
        if lvl = 0 then
          (* Atom true at level 0 gives a trivially true clause *)
          raise Trivial;
        Vec.push trues a
      ) else if Atom.is_false store a then (
        let lvl = Atom.level store a in
        if lvl = 0 then (
          (* Atom var false at level 0 can be eliminated from the clause,
             but we need to kepp in mind that we used another clause to simplify it. *)
          Log.debugf 50 (fun k ->
              k "(@[sat.preprocess-clause.resolve-away-lvl0@ %a@])"
                (Atom.debug store) a);

          let p = proof_of_atom_lvl0_ self (Atom.neg a) in
          add_proof_lvl0_ p
        ) else
          Vec.push falses a
      ) else
        Vec.push unassigned a
    )
  in

  (try
     Clause.iter store c ~f:consider_atom;
     cleanup ()
   with e ->
     cleanup ();
     raise e);

  (* merge all atoms together *)
  let atoms =
    let v = trues in
    Vec.append ~into:v unassigned;
    Vec.append ~into:v falses;
    Vec.to_array v
  in

  if !res0_proofs = [] then
    (* no change except in the order of literals *)
    Clause.make_a store atoms ~removable:(Clause.removable store c)
      (Clause.proof_step store c)
  else (
    assert (Array.length atoms < Clause.n_atoms store c);
    (* some atoms were removed by resolution with level-0 clauses *)
    Log.debugf 30 (fun k ->
        k "(@[sat.add-clause.resolved-lvl-0@ :into [@[%a@]]@])"
          (Atom.debug_a store) atoms);
    let proof =
      Proof_trace.add_step self.proof @@ fun () ->
      let lits = Util.array_to_list_map (Atom.lit store) atoms in
      let hyps =
        Iter.(cons (Clause.proof_step self.store c) (of_list !res0_proofs))
      in
      Proof_sat.sat_redundant_clause lits ~hyps
    in
    Clause.make_a store atoms proof ~removable:(Clause.removable store c)
  )

let new_decision_level (self : t) =
  assert (self.th_head = AVec.size self.trail);
  assert (self.elt_head = AVec.size self.trail);
  Veci.push self.var_levels (AVec.size self.trail);
  let (module P) = self.plugin in
  P.push_level ();
  ()

(* Attach/Detach a clause.

   Atom clause is attached (to its watching lits) when it is first added,
   either because it is assumed or learnt.
*)
let attach_clause (self : t) c =
  let store = self.store in
  assert (not @@ Clause.attached store c);
  Log.debugf 20 (fun k ->
      k "(@[sat.attach-clause@ %a@])" (Clause.debug store) c);
  (* TODO: change when watchlist are updated *)
  CVec.push (Atom.watched store (Atom.neg (Clause.atoms_a store c).(0))) c;
  CVec.push (Atom.watched store (Atom.neg (Clause.atoms_a store c).(1))) c;
  Clause.set_attached store c true;
  ()

(* Backtracking.
   Used to backtrack, i.e cancel down to [lvl] excluded,
   i.e we want to go back to the state the solver was in
       after decision level [lvl] was created and fully propagated. *)
let cancel_until (self : t) lvl =
  let store = self.store in
  assert (lvl >= 0);
  (* Nothing to do if we try to backtrack to a non-existent level. *)
  if decision_level self <= lvl then
    Log.debugf 20 (fun k ->
        k "(@[sat.cancel-until.nop@ :already-at-level <= %d@])" lvl)
  else (
    Log.debugf 5 (fun k -> k "(@[sat.cancel-until %d@])" lvl);
    (* We set the head of the solver and theory queue to what it was. *)
    let head = ref (Veci.get self.var_levels lvl) in
    self.elt_head <- !head;
    self.th_head <- !head;
    (* Now we need to cleanup the vars that are not valid anymore
       (i.e to the right of elt_head in the queue. *)
    for c = self.elt_head to AVec.size self.trail - 1 do
      let a = AVec.get self.trail c in
      (* Atom literal is unassigned, we nedd to add it back to
         the heap of potentially assignable literals, unless it has
         a level lower than [lvl], in which case we just move it back. *)
      (* Atom variable is not true/false anymore, one of two things can happen: *)
      if Atom.level store a <= lvl then (
        (* It is a late propagation, which has a level
           lower than where we backtrack, so we just move it to the head
           of the queue, to be propagated again. *)
        AVec.set self.trail !head a;
        head := !head + 1
      ) else (
        (* it is a result of bolean propagation, or a semantic propagation
           with a level higher than the level to which we backtrack,
           in that case, we simply unset its value and reinsert it into the heap. *)
        Atom.set_is_true store a false;
        Atom.set_is_true store (Atom.neg a) false;
        Var.set_level store (Atom.var a) (-1);
        Var.set_reason store (Atom.var a) None;
        insert_var_order self (Atom.var a)
      )
    done;
    (* Recover the right theory state. *)
    let n = decision_level self - lvl in
    assert (n > 0);
    (* Resize the vectors according to their new size. *)
    AVec.shrink self.trail !head;
    Veci.shrink self.var_levels lvl;
    let (module P) = self.plugin in
    P.pop_levels n;
    Delayed_actions.clear_on_backtrack self.delayed_actions;
    (* TODO: for scoped clause pools, backtrack them *)
    self.next_decisions <- []
  );
  ()

let pp_unsat_cause self out = function
  | US_local { first = _; core } ->
    Format.fprintf out "(@[unsat-cause@ :false-assumptions %a@])"
      (Format.pp_print_list (Atom.pp self.store))
      core
  | US_false c ->
    Format.fprintf out "(@[unsat-cause@ :false %a@])" (Clause.debug self.store)
      c

(* Unsatisfiability is signaled through an exception, since it can happen
   in multiple places (adding new clauses, or solving for instance). *)
let report_unsat self (us : unsat_cause) : _ =
  Log.debugf 3 (fun k ->
      k "(@[sat.unsat-conflict@ %a@])" (pp_unsat_cause self) us);
  let us =
    match us with
    | US_false c ->
      self.unsat_at_0 <- Some c;
      Event.emit self.on_learnt c;
      let p = Clause.proof_step self.store c in
      Proof_trace.add_unsat self.proof p;
      US_false c
    | US_local _ -> us
  in
  raise (E_unsat us)

(* Boolean propagation.
   Wrapper function for adding a new propagated lit. *)
let enqueue_bool (self : t) a ~level:lvl reason : unit =
  let store = self.store in
  if Atom.is_false store a then (
    Log.debugf 0 (fun k ->
        k "(@[sat.error.trying to enqueue a false literal %a@])"
          (Atom.debug store) a);
    assert false
  );
  assert (
    (not (Atom.is_true store a))
    && Atom.level store a < 0
    && Atom.reason store a == None
    && lvl >= 0);
  (* backtrack if required *)
  if lvl < decision_level self then cancel_until self lvl;
  Atom.set_is_true store a true;
  Var.set_level store (Atom.var a) lvl;
  Var.set_reason store (Atom.var a) (Some reason);
  AVec.push self.trail a;
  Log.debugf 20 (fun k ->
      k "(@[sat.enqueue[%d]@ %a@])" (AVec.size self.trail) (Atom.debug store) a);
  ()

(* swap elements of array *)
let[@inline] swap_arr a i j =
  if i <> j then (
    let tmp = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- tmp
  )

(* move atoms assigned at high levels first *)
let put_high_level_atoms_first (store : store) (arr : atom array) : unit =
  Array.iteri
    (fun i a ->
      if i > 0 && Atom.level store a > Atom.level store arr.(0) then
        if (* move first to second, [i]-th to first, second to [i] *)
           i = 1 then
          swap_arr arr 0 1
        else (
          let tmp = arr.(1) in
          arr.(1) <- arr.(0);
          arr.(0) <- arr.(i);
          arr.(i) <- tmp
        )
      else if i > 1 && Atom.level store a > Atom.level store arr.(1) then
        swap_arr arr 1 i)
    arr

(* find which level to backtrack to, given a conflict clause
   and a boolean stating whether it is
   a UIP ("Unique Implication Point")
   precond: the atom list is sorted by decreasing decision level *)
let backtrack_lvl (self : t) (arr : atom array) : int * bool =
  let store = self.store in
  if Array.length arr <= 1 then
    0, true
  else (
    let a = arr.(0) in
    let b = arr.(1) in
    assert (Atom.level store a > 0);
    if Atom.level store a > Atom.level store b then
      ( (* backtrack below [a], so we can propagate [not a] *)
        Atom.level store b,
        true )
    else (
      assert (Atom.level store a = Atom.level store b);
      assert (Atom.level store a >= 0);
      max (Atom.level store a - 1) 0, false
    )
  )

(* abtraction of the assignment level of [v] in an integer *)
let[@inline] abstract_level_ (self : t) (v : var) : int =
  1 lsl (Var.level self.store v land 31)

exception Non_redundant

(* can we remove [a] by self-subsuming resolutions with other lits
   of the learnt clause? *)
let lit_redundant (self : t) (abstract_levels : int) (steps : Step_vec.t)
    (v : var) : bool =
  let store = self.store in
  let to_unmark = self.to_clear in
  let steps_size_init = Step_vec.size steps in

  (* save current state of [to_unmark] *)
  let top = Vec.size to_unmark in
  let rec aux v =
    match Var.reason store v with
    | None -> assert false
    | Some Decision -> raise_notrace Non_redundant
    | Some (Bcp c | Bcp_lazy (lazy c)) ->
      let c_atoms = Clause.atoms_a store c in
      assert (Var.equal v (Atom.var c_atoms.(0)));
      if Proof_trace.enabled self.proof then
        Step_vec.push steps (Clause.proof_step self.store c);

      (* check that all the other lits of [c] are marked or redundant *)
      for i = 1 to Array.length c_atoms - 1 do
        let v2 = Atom.var c_atoms.(i) in
        let lvl_v2 = Var.level store v2 in
        if not (Var.marked store v2) then (
          match Var.reason store v2 with
          | None -> assert false
          | _ when lvl_v2 = 0 ->
            (* can always remove literals at level 0, but got
               to update proof properly *)
            if Proof_trace.enabled self.proof then (
              let p = proof_of_atom_lvl0_ self (Atom.neg c_atoms.(i)) in
              Step_vec.push steps p
            )
          | Some (Bcp _ | Bcp_lazy _)
            when abstract_level_ self v2 land abstract_levels <> 0 ->
            (* possibly removable, its level may comprise an atom in learnt clause *)
            Vec.push to_unmark v2;
            Var.mark store v2;
            aux v2
          | Some _ -> raise_notrace Non_redundant
        )
      done
  in
  try
    aux v;
    true
  with Non_redundant ->
    (* clear new marks, they are not actually redundant *)
    for i = top to Vec.size to_unmark - 1 do
      Var.unmark store (Vec.get to_unmark i)
    done;
    Vec.shrink to_unmark top;
    Step_vec.shrink steps steps_size_init;
    (* restore proof *)
    false

(* minimize conflict by removing atoms whose propagation history
   is ultimately self-subsuming with [lits] *)
let minimize_conflict (self : t) (_c_level : int) (learnt : AVec.t)
    (steps : Step_vec.t) : unit =
  let store = self.store in

  (* abstraction of the levels involved in the conflict at all,
     as logical "or" of each literal's approximate level *)
  let abstract_levels =
    AVec.fold_left
      (fun lvl a -> lvl lor abstract_level_ self (Atom.var a))
      0 learnt
  in

  let j = ref 1 in
  for i = 1 to AVec.size learnt - 1 do
    let a = AVec.get learnt i in
    let keep =
      match Atom.reason store a with
      | Some Decision -> true (* always keep decisions *)
      | Some (Bcp _ | Bcp_lazy _) ->
        not (lit_redundant self abstract_levels steps (Atom.var a))
      | None -> assert false
    in
    if keep then (
      AVec.set learnt !j a;
      incr j
    ) else
      Stat.incr self.n_minimized_away
  done;
  AVec.shrink learnt !j;
  ()

(* result of conflict analysis, containing the learnt clause and some
   additional info. *)
type conflict_res = {
  cr_backtrack_lvl: int; (* level to backtrack to *)
  cr_learnt: atom array; (* lemma learnt from conflict *)
  cr_is_uip: bool; (* conflict is UIP? *)
  cr_steps: Step_vec.t;
}

(* conflict analysis, starting with top of trail and conflict clause *)
let analyze (self : t) (c_clause : clause) : conflict_res =
  let store = self.store in

  let to_unmark = self.to_clear in
  (* for cleanup *)
  Vec.clear to_unmark;
  let learnt = self.temp_atom_vec in
  AVec.clear learnt;

  let steps = self.temp_step_vec in
  (* for proof *)
  assert (Step_vec.is_empty steps);

  (* loop variables *)
  let pathC = ref 0 in
  let continue = ref true in
  let blevel = ref 0 in
  let c = ref (Some c_clause) in
  (* current clause to analyze/resolve *)
  let tr_ind = ref (AVec.size self.trail - 1) in

  (* pointer in trail *)

  (* conflict level *)
  assert (decision_level self > 0);
  let conflict_level =
    let (module P) = self.plugin in
    if P.has_theory then
      Clause.fold store 0 c_clause ~f:(fun acc p ->
          max acc (Atom.level store p))
    else
      decision_level self
  in
  Log.debugf 30 (fun k ->
      k "(@[sat.analyze-conflict@ :c-level %d@ :clause %a@])" conflict_level
        (Clause.debug store) c_clause);

  while !continue do
    (match !c with
    | None ->
      Log.debug 30
        "(@[sat.analyze-conflict: skipping resolution for semantic \
         propagation@])"
    | Some clause ->
      Log.debugf 30 (fun k ->
          k "(@[sat.analyze-conflict.resolve@ %a@])" (Clause.debug store) clause);

      if Clause.removable store clause then clause_bump_activity self clause;
      if Proof_trace.enabled self.proof then
        Step_vec.push steps (Clause.proof_step self.store clause);

      (* visit the current predecessors *)
      let atoms = Clause.atoms_a store clause in
      for j = 0 to Array.length atoms - 1 do
        let q = atoms.(j) in
        assert (Atom.has_value store q);
        assert (Atom.level store q >= 0);
        if Atom.level store q = 0 then (
          (* skip [q] entirely, resolved away at level 0 *)
          assert (Atom.is_false store q);
          if Proof_trace.enabled self.proof then (
            let step = proof_of_atom_lvl0_ self (Atom.neg q) in
            Step_vec.push steps step
          )
        ) else if not (Var.marked store (Atom.var q)) then (
          Var.mark store (Atom.var q);
          Vec.push to_unmark (Atom.var q);
          if Atom.level store q > 0 then (
            var_bump_activity self (Atom.var q);
            if Atom.level store q >= conflict_level then
              incr pathC
            else (
              AVec.push learnt q;
              blevel := max !blevel (Atom.level store q)
            )
          )
        )
      done);

    (* look for the next node to expand *)
    while
      let a = AVec.get self.trail !tr_ind in
      Log.debugf 30 (fun k ->
          k "(@[sat.analyze-conflict.at-trail-elt@ %a@])" (Atom.debug store) a);
      (not (Var.marked store (Atom.var a)))
      || Atom.level store a < conflict_level
    do
      decr tr_ind
    done;
    let p = AVec.get self.trail !tr_ind in
    decr pathC;
    decr tr_ind;
    match !pathC, Atom.reason store p with
    | 0, _ ->
      continue := false;
      AVec.push learnt (Atom.neg p)
    | n, Some (Bcp cl | Bcp_lazy (lazy cl)) ->
      assert (n > 0);
      assert (Atom.level store p >= conflict_level);
      c := Some cl
    | _, (None | Some Decision) -> assert false
  done;

  Log.debugf 10 (fun k ->
      k "(@[sat.conflict.res@ %a@])" (AVec.pp @@ Atom.debug store) learnt);

  (* minimize conflict, to get a more general lemma *)
  minimize_conflict self conflict_level learnt steps;

  let cr_steps = Step_vec.copy steps in
  Step_vec.clear self.temp_step_vec;

  (* cleanup marks *)
  Vec.iter ~f:(Store.clear_var store) to_unmark;
  Vec.clear to_unmark;

  (* put high-level literals first, so that:
     - they make adequate watch lits
     - the first literal is the UIP, if any *)
  let cr_learnt = AVec.to_array learnt in
  AVec.clear learnt;
  Array.sort
    (fun p q -> compare (Atom.level store q) (Atom.level store p))
    cr_learnt;

  (* put_high_level_atoms_first a; *)
  let level, is_uip = backtrack_lvl self cr_learnt in
  Log.debugf 10 (fun k ->
      k "(@[sat.conflict.res.final@ :lvl %d@ {@[%a@]}@])" level
        (Util.pp_array @@ Atom.debug store)
        cr_learnt);

  { cr_backtrack_lvl = level; cr_learnt; cr_is_uip = is_uip; cr_steps }

(* Get the correct vector to insert a clause in. *)
let[@inline] add_clause_to_vec_ ~pool self c =
  if Clause.removable self.store c && Clause.n_atoms self.store c > 2 then
    (* add clause to some pool/set of clauses *)
    cp_add_ pool c
  else
    CVec.push self.clauses_hyps c

(* add the learnt clause to the clause database, propagate, etc. *)
let record_learnt_clause (self : t) ~pool (cr : conflict_res) : unit =
  let store = self.store in
  (match cr.cr_learnt with
  | [||] -> assert false
  | [| fuip |] ->
    assert (cr.cr_backtrack_lvl = 0 && decision_level self = 0);

    let p =
      Proof_trace.add_step self.proof @@ fun () ->
      let lits = Util.array_to_list_map (Atom.lit self.store) cr.cr_learnt in
      Proof_sat.sat_redundant_clause lits ~hyps:(Step_vec.to_iter cr.cr_steps)
    in
    let uclause = Clause.make_a store ~removable:true cr.cr_learnt p in
    Event.emit self.on_learnt uclause;

    if Atom.is_false store fuip then
      (* incompatible at level 0 *)
      report_unsat self (US_false uclause)
    else
      (* no need to attach [uclause], it is true at level 0 *)
      enqueue_bool self fuip ~level:0 (Bcp uclause)
  | _ ->
    let fuip = cr.cr_learnt.(0) in
    let p =
      Proof_trace.add_step self.proof @@ fun () ->
      let lits = Util.array_to_list_map (Atom.lit self.store) cr.cr_learnt in
      Proof_sat.sat_redundant_clause lits ~hyps:(Step_vec.to_iter cr.cr_steps)
    in
    let lclause = Clause.make_a store ~removable:true cr.cr_learnt p in

    add_clause_to_vec_ ~pool self lclause;
    attach_clause self lclause;
    clause_bump_activity self lclause;
    Event.emit self.on_learnt lclause;
    assert cr.cr_is_uip;
    enqueue_bool self fuip ~level:cr.cr_backtrack_lvl (Bcp lclause));
  var_decay_activity self;
  clause_decay_activity self

(* process a conflict:
   - learn clause
   - backtrack
   - report unsat if conflict at level 0
*)
let add_boolean_conflict (self : t) (confl : clause) : unit =
  let store = self.store in
  Log.debugf 5 (fun k ->
      k "(@[sat.add-bool-conflict@ %a@])" (Clause.debug store) confl);
  self.next_decisions <- [];
  assert (decision_level self >= 0);
  if
    decision_level self = 0
    || Clause.for_all store confl ~f:(fun a -> Atom.level store a <= 0)
  then
    (* Top-level conflict *)
    report_unsat self (US_false confl);
  let cr = analyze self confl in
  cancel_until self (max cr.cr_backtrack_lvl 0);
  record_learnt_clause ~pool:self.clauses_learnt self cr

(* Add a new clause, simplifying, propagating, and backtracking if
   the clause is false in the current trail *)
let add_clause_ (self : t) ~pool (init : clause) : unit =
  let store = self.store in
  Log.debugf 30 (fun k ->
      k "(@[sat.add-clause@ @[<hov>%a@]@])" (Clause.debug store) init);
  (* Insertion of new lits is done before simplification. Indeed, else a lit in a
     trivial clause could end up being not decided on, which is a bug. *)
  Clause.iter store init ~f:(fun x -> insert_var_order self (Atom.var x));
  try
    (* preprocess to remove dups, sort literals, etc. *)
    let clause = preprocess_clause_ self init in
    assert (Clause.removable store clause = Clause.removable store init);

    Log.debugf 5 (fun k ->
        k "(@[sat.new-clause@ @[<hov>%a@]@])" (Clause.debug store) clause);
    let atoms = Clause.atoms_a self.store clause in
    match atoms with
    | [||] -> report_unsat self @@ US_false clause
    | [| a |] ->
      cancel_until self 0;
      if Atom.is_false store a then
        (* cannot recover from this *)
        report_unsat self @@ US_false clause
      else if Atom.is_true store a then
        ()
      (* atom is already true, (at level 0) nothing to do *)
      else (
        Log.debugf 40 (fun k ->
            k "(@[sat.add-clause.unit-clause@ :propagating %a@])"
              (Atom.debug store) a);
        add_clause_to_vec_ ~pool self clause;
        enqueue_bool self a ~level:0 (Bcp clause)
      )
    | _ ->
      let a = atoms.(0) in
      let b = atoms.(1) in
      add_clause_to_vec_ ~pool self clause;
      if Atom.is_false store a then (
        (* Atom need to be sorted in decreasing order of decision level,
           or we might watch the wrong literals. *)
        put_high_level_atoms_first store (Clause.atoms_a store clause);
        attach_clause self clause;
        add_boolean_conflict self clause
      ) else (
        attach_clause self clause;
        if Atom.is_false store b && not (Atom.has_value store a) then (
          (* unit, propagate [a] *)
          let lvl =
            Array.fold_left (fun m a -> max m (Atom.level store a)) 0 atoms
          in
          cancel_until self lvl;
          Log.debugf 50 (fun k ->
              k "(@[sat.add-clause.propagate@ %a@ :lvl %d@])" (Atom.debug store)
                a lvl);
          enqueue_bool self a ~level:lvl (Bcp clause)
        )
      )
  with Trivial ->
    Log.debugf 5 (fun k ->
        k "(@[sat.add-clause@ :ignore-trivial @[%a@]@])" (Clause.debug store)
          init)

type watch_res = Watch_kept | Watch_removed

(* boolean propagation.
   [a] is the false atom, one of [c]'s two watch literals
   [i] is the index of [c] in [a.watched]
   @return whether [c] was removed from [a.watched]
*)
let propagate_in_clause (self : t) (a : atom) (c : clause) (i : int) : watch_res
    =
  let store = self.store in
  let atoms = Clause.atoms_a store c in
  let first = atoms.(0) in
  if first = Atom.neg a then (
    (* false lit must be at index 1 *)
    atoms.(0) <- atoms.(1);
    atoms.(1) <- first
  ) else
    assert (Atom.neg a = atoms.(1));
  let first = atoms.(0) in
  if Atom.is_true store first then
    Watch_kept
  (* true clause, keep it in watched *)
  else (
    try
      (* look for another watch lit *)
      for k = 2 to Array.length atoms - 1 do
        let ak = atoms.(k) in
        if not (Atom.is_false store ak) then (
          (* watch lit found: update and exit *)
          atoms.(1) <- ak;
          atoms.(k) <- Atom.neg a;
          (* remove [c] from [a.watched], add it to [ak.neg.watched] *)
          CVec.push (Atom.watched store (Atom.neg ak)) c;
          assert (Clause.equal (CVec.get (Atom.watched store a) i) c);
          CVec.fast_remove (Atom.watched store a) i;
          raise_notrace Exit
        )
      done;
      (* no watch lit found *)
      if Atom.is_false store first then (
        (* clause is false *)
        self.elt_head <- AVec.size self.trail;
        raise_notrace (Conflict c)
      ) else (
        Stat.incr self.n_propagations;
        enqueue_bool self first ~level:(decision_level self) (Bcp c)
      );
      Watch_kept
    with Exit -> Watch_removed
  )

(* propagate atom [a], which was just decided. This checks every
   clause watching [a] to see if the clause is false, unit, or has
   other possible watches
   @param res the optional conflict clause that the propagation might trigger *)
let propagate_atom (self : t) a : unit =
  let store = self.store in
  let watched = Atom.watched store a in
  let rec aux i =
    if i >= CVec.size watched then
      ()
    else (
      let c = CVec.get watched i in
      assert (Clause.attached store c);
      let j =
        if Clause.dead store c then
          i
        (* remove on the fly *)
        else (
          match propagate_in_clause self a c i with
          | Watch_kept -> i + 1
          | Watch_removed -> i (* clause at this index changed *)
        )
      in
      aux j
    )
  in
  aux 0

exception Th_conflict of Clause.t

let acts_add_clause self ?(keep = false) (l : Lit.t list) (p : Proof_step.id) :
    unit =
  let atoms = List.rev_map (make_atom_ self) l in
  let removable = not keep in
  let c = Clause.make_l self.store ~removable atoms p in
  Log.debugf 5 (fun k ->
      k "(@[sat.th.add-clause@ %a@])" (Clause.debug self.store) c);
  (* will be added later, even if we backtrack *)
  Delayed_actions.add_clause_learnt self.delayed_actions c

let acts_add_decision_lit (self : t) (f : Lit.t) (sign : bool) : unit =
  let store = self.store in
  let a = make_atom_ self f in
  let a =
    if sign then
      a
    else
      Atom.neg a
  in
  if not (Atom.has_value store a) then (
    Log.debugf 10 (fun k ->
        k "(@[sat.th.add-decision-lit@ %a@])" (Atom.debug store) a);
    Delayed_actions.add_decision self.delayed_actions a
  )

let acts_raise self (l : Lit.t list) (p : Proof_step.id) : 'a =
  let atoms = List.rev_map (make_atom_ self) l in
  (* conflicts can be removed *)
  let c = Clause.make_l self.store ~removable:true atoms p in
  Log.debugf 5 (fun k ->
      k "(@[@{<yellow>sat.th.raise-conflict@}@ %a@])" (Clause.debug self.store)
        c);
  (* we can shortcut the rest of the theory propagations *)
  raise_notrace (Th_conflict c)

let check_consequence_lits_false_ self l p : unit =
  let store = self.store in
  Log.debugf 50 (fun k ->
      k "(@[sat.check-consequence-lits: %a@ :for %a@])"
        (Util.pp_list (Atom.debug store))
        l (Atom.debug store) p);
  match List.find (fun a -> Atom.is_true store a) l with
  | a ->
    invalid_argf
      "slice.acts_propagate:@ Consequence should contain only false literals,@ \
       but @[%a@] is true"
      (Atom.debug store) (Atom.neg a)
  | exception Not_found -> ()

let acts_propagate (self : t) f (expl : reason) =
  let store = self.store in
  match expl with
  | Consequence mk_expl ->
    let p = make_atom_ self f in
    Log.debugf 30 (fun k ->
        k "(@[sat.propagate-from-theory@ %a@])" (Atom.debug store) p);
    if Atom.is_true store p then
      ()
    else if Atom.is_false store p then (
      let lits, proof = mk_expl () in
      let guard = List.rev_map (fun f -> Atom.neg @@ make_atom_ self f) lits in
      check_consequence_lits_false_ self guard p;
      let c = Clause.make_l store ~removable:true (p :: guard) proof in
      raise_notrace (Th_conflict c)
    ) else (
      insert_var_order self (Atom.var p);
      let c, level =
        (* Check literals + proof eagerly, as it's safer.

           We could check invariants in a [lazy] block,
           as conflict analysis would run in an environment where
           the literals should be true anyway, since it's an extension of the
           current trail.
           (otherwise the propagated lit would have been backtracked and
           discarded already.)

           However it helps catching propagation bugs to verify truthiness
           of the guard (and level) eagerly.
        *)
        let lits, proof = mk_expl () in
        let guard =
          List.rev_map (fun f -> Atom.neg @@ make_atom_ self f) lits
        in
        check_consequence_lits_false_ self guard p;
        let level =
          List.fold_left (fun l a -> max l (Atom.level store a)) 0 guard
        in
        assert (level <= decision_level self);
        (* delay creating the actual clause. *)
        lazy (Clause.make_l store ~removable:true (p :: guard) proof), level
      in
      Delayed_actions.propagate_atom self.delayed_actions p ~lvl:level c
    )

let[@inline never] perform_delayed_actions_ (self : t) : unit =
  let add_clause_learnt c = add_clause_ ~pool:self.clauses_learnt self c
  and add_clause_pool c pool = add_clause_ ~pool self c
  and decision a = self.next_decisions <- a :: self.next_decisions
  and propagate p ~lvl c =
    if Atom.is_true self.store p then
      ()
    else if Atom.is_false self.store p then
      raise_notrace (Th_conflict (Lazy.force c))
    else (
      Stat.incr self.n_propagations;
      enqueue_bool self p ~level:lvl (Bcp_lazy c)
    )
  in
  Delayed_actions.iter self.delayed_actions ~add_clause_learnt ~add_clause_pool
    ~propagate ~decision;
  ()

let[@inline] has_no_delayed_actions (self : t) : bool =
  Delayed_actions.is_empty self.delayed_actions

let[@inline] perform_delayed_actions self =
  if not (has_no_delayed_actions self) then perform_delayed_actions_ self

let[@specialise] acts_iter self ~full head f : unit =
  for
    i =
      if full then
        0
      else
        head to AVec.size self.trail - 1
  do
    let a = AVec.get self.trail i in
    f (Atom.lit self.store a)
  done

let eval_atom_ self a =
  if Atom.is_true self.store a then
    L_true
  else if Atom.is_false self.store a then
    L_false
  else
    L_undefined

let[@inline] acts_eval_lit self (f : Lit.t) : lbool =
  let a = make_atom_ self f in
  eval_atom_ self a

let[@inline] acts_add_lit self ?default_pol f : unit =
  ignore (make_atom_ ?default_pol self f : atom)

let[@inline] current_slice st : acts =
  let module M = struct
    let proof = st.proof
    let iter_assumptions = acts_iter st ~full:false st.th_head
    let eval_lit = acts_eval_lit st
    let add_lit = acts_add_lit st
    let add_clause = acts_add_clause st
    let propagate = acts_propagate st
    let raise_conflict c pr = acts_raise st c pr
    let add_decision_lit = acts_add_decision_lit st
  end in
  (module M)

(* full slice, for [if_sat] final check *)
let[@inline] full_slice st : acts =
  let module M = struct
    let proof = st.proof
    let iter_assumptions = acts_iter st ~full:true st.th_head
    let eval_lit = acts_eval_lit st
    let add_lit = acts_add_lit st
    let add_clause = acts_add_clause st
    let propagate = acts_propagate st
    let raise_conflict c pr = acts_raise st c pr
    let add_decision_lit = acts_add_decision_lit st
  end in
  (module M)

(* Assert that the conflict is indeeed a conflict *)
let check_is_conflict_ self (c : Clause.t) : unit =
  if not @@ Clause.for_all self.store c ~f:(Atom.is_false self.store) then (
    Log.debugf 0 (fun k ->
        k "conflict should be false: %a" (Clause.debug self.store) c);
    assert false
  )

(* some boolean literals were decided/propagated within Msat. Now we
   need to inform the theory of those assumptions, so it can do its job.
   @return the conflict clause, if the theory detects unsatisfiability *)
let rec theory_propagate self : clause option =
  assert (self.elt_head = AVec.size self.trail);
  assert (self.th_head <= self.elt_head);
  if self.th_head = self.elt_head then
    None
  (* fixpoint/no propagation *)
  else (
    let slice = current_slice self in
    self.th_head <- self.elt_head;
    (* catch up *)
    let (module P) = self.plugin in
    match P.partial_check slice with
    | () ->
      perform_delayed_actions self;
      propagate self
    | exception Th_conflict c ->
      check_is_conflict_ self c;
      Clause.iter self.store c ~f:(fun a -> insert_var_order self (Atom.var a));
      Some c
  )

(* fixpoint between boolean propagation and theory propagation
   @return a conflict clause, if any *)
and propagate (st : t) : clause option =
  (* First, treat the stack of lemmas/actions added by the theory, if any *)
  perform_delayed_actions st;
  (* Now, check that the situation is sane *)
  assert (st.elt_head <= AVec.size st.trail);
  if st.elt_head = AVec.size st.trail then
    theory_propagate st
  else (
    match
      while st.elt_head < AVec.size st.trail do
        let a = AVec.get st.trail st.elt_head in
        propagate_atom st a;
        st.elt_head <- st.elt_head + 1
      done
    with
    | () -> theory_propagate st
    | exception Conflict c -> Some c
  )

(* compute unsat core from assumption [a] *)
let analyze_final (self : t) (a : atom) : atom list =
  let store = self.store in
  Log.debugf 5 (fun k ->
      k "(@[sat.analyze-final@ :lit %a@])" (Atom.debug store) a);
  assert (Atom.is_false store a);
  let core = ref [ a ] in
  let idx = ref (AVec.size self.trail - 1) in
  Var.mark store (Atom.var a);
  let seen = ref [ Atom.var a ] in
  while !idx >= 0 do
    let a' = AVec.get self.trail !idx in
    if Var.marked store (Atom.var a') then (
      match Atom.reason store a' with
      | Some Decision -> core := a' :: !core
      | Some (Bcp c | Bcp_lazy (lazy c)) ->
        Clause.iter store c ~f:(fun a ->
            let v = Atom.var a in
            if not (Var.marked store v) then (
              seen := v :: !seen;
              Var.mark store v
            ))
      | None -> ()
    );
    decr idx
  done;
  List.iter (Var.unmark store) !seen;
  Log.debugf 5 (fun k ->
      k "(@[sat.analyze-final.done@ :core %a@])"
        (Format.pp_print_list (Atom.debug store))
        !core);
  !core

(* GC: remove some learnt clauses.
   This works even during the proof with a non empty trail. *)
let reduce_clause_db (self : t) : unit =
  let store = self.store in

  Log.debugf 3 (fun k ->
      k "(@[sat.gc-clauses.start :max-learnt %d@])" !(self.max_clauses_learnt));

  let to_be_gc = self.temp_clause_vec in
  (* clauses to collect *)
  assert (CVec.is_empty to_be_gc);

  (* atoms whose watches will need to be rebuilt to filter out
     dead clauses *)
  let dirty_atoms = self.temp_atom_vec in
  assert (AVec.is_empty dirty_atoms);

  (* [a] is watching at least one removed clause, we'll need to
     trim its watchlist *)
  let[@inline] mark_dirty_atom a =
    if not (Atom.marked store a) then (
      Atom.mark store a;
      AVec.push dirty_atoms a
    )
  in

  (* iter on the clauses that are used to explain atoms on the trail,
     which we must therefore keep for now as they might participate in
     conflict resolution *)
  let iter_clauses_on_trail ~f : unit =
    AVec.iter self.trail ~f:(fun a ->
        match Atom.reason store a with
        | Some (Bcp c) -> f c
        | Some (Bcp_lazy lc) when Lazy.is_val lc -> f (Lazy.force lc)
        | _ -> ())
  in

  iter_clauses_on_trail ~f:(fun c -> Clause.set_marked store c true);

  (* first, mark clauses used on the trail, we cannot GC them.
     TODO: once we use DRUP, we can avoid marking level-0 explanations
     as they will never participate in resolution. *)
  AVec.iter
    ~f:(fun a ->
      match Atom.reason store a with
      | Some (Bcp c) -> Clause.set_marked store c true
      | Some (Bcp_lazy lc) when Lazy.is_val lc ->
        Clause.set_marked store (Lazy.force lc) true
      | _ -> ())
    self.trail;

  (* GC the clause [c] *)
  let flag_clause_for_gc c : unit =
    assert (Clause.removable store c);
    Log.debugf 10 (fun k ->
        k "(@[sat.gc.will-collect@ %a@])" (Clause.debug store) c);
    CVec.push to_be_gc c;
    Clause.set_dead store c true;
    let atoms = Clause.atoms_a store c in
    mark_dirty_atom (Atom.neg atoms.(0));
    (* need to remove from watchlists *)
    mark_dirty_atom (Atom.neg atoms.(1));
    Event.emit self.on_gc (Clause.lits_a store c);
    Proof_trace.delete self.proof (Clause.proof_step store c)
  in

  let gc_arg =
    (module struct
      let store = self.store
      let flag_clause_for_gc = flag_clause_for_gc
      let must_keep_clause c = Clause.marked store c
    end : GC_ARG)
  in

  (* GC a pool, if it needs it *)
  let gc_pool (module P : CLAUSE_POOL) : unit =
    if P.needs_gc () then (
      Log.debugf 5 (fun k -> k "(@[sat.gc.pool@ :descr %s@])" (P.descr ()));
      P.gc gc_arg
    )
  in

  gc_pool self.clauses_learnt;
  Vec.iter ~f:gc_pool self.clause_pools;

  let n_collected = CVec.size to_be_gc in

  (* update watchlist of dirty atoms *)
  AVec.iter dirty_atoms ~f:(fun a ->
      assert (Atom.marked store a);
      Atom.unmark store a;
      let w = Atom.watched store a in
      CVec.filter_in_place (fun c -> not (Clause.dead store c)) w);
  AVec.clear dirty_atoms;

  (* actually remove the clauses now that they are detached *)
  CVec.iter ~f:(Clause.dealloc store) to_be_gc;
  CVec.clear to_be_gc;

  (* remove marks on clauses on the trail *)
  iter_clauses_on_trail ~f:(fun c -> Clause.set_marked store c false);

  Log.debugf 3 (fun k -> k "(@[sat.gc.done :collected %d@])" n_collected);
  ()

(* Decide on a new literal, and enqueue it into the trail.
   Return [true] if a decision was made.
   @param full if true, do decisions;
   if false, only pick from [self.next_decisions]
   and [self.assumptions] *)
let pick_branch_lit ~full self : bool =
  let rec pick_lit () =
    match self.next_decisions with
    | atom :: tl ->
      self.next_decisions <- tl;
      pick_with_given_atom atom
    | [] when decision_level self < AVec.size self.assumptions ->
      (* use an assumption *)
      let a = AVec.get self.assumptions (decision_level self) in
      if Atom.is_true self.store a then (
        new_decision_level self;
        (* pseudo decision level, [a] is already true *)
        pick_lit ()
      ) else if Atom.is_false self.store a then (
        (* root conflict, find unsat core *)
        let core = analyze_final self a in
        raise (E_unsat (US_local { first = a; core }))
      ) else
        pick_with_given_atom a
    | [] when not full -> false
    | [] ->
      (match H.remove_min self.order with
      | v ->
        pick_with_given_atom
          (if Var.default_pol self.store v then
            Atom.pa v
          else
            Atom.na v)
      | exception Not_found -> false)
  (* pick a decision, trying [atom] first if it's not assigned yet. *)
  and pick_with_given_atom (atom : atom) : bool =
    let v = Atom.var atom in
    if Var.level self.store v >= 0 then (
      assert (
        Atom.is_true self.store (Atom.pa v)
        || Atom.is_true self.store (Atom.na v));
      pick_lit ()
    ) else (
      new_decision_level self;
      let current_level = decision_level self in
      enqueue_bool self atom ~level:current_level Decision;
      Stat.incr self.n_decisions;
      Event.emit self.on_decision (Atom.lit self.store atom);
      true
    )
  in
  pick_lit ()

(* do some amount of search, until the number of conflicts or clause learnt
   reaches the given parameters *)
let search (self : t) ~on_progress ~(max_conflicts : int) : unit =
  let@ () = Profile.with_ "sat.search" in
  Log.debugf 3 (fun k ->
      k "(@[sat.search@ :max-conflicts %d@ :max-learnt %d@])" max_conflicts
        !(self.max_clauses_learnt));
  let n_conflicts = ref 0 in
  while true do
    match propagate self with
    | Some confl ->
      (* Conflict *)
      incr n_conflicts;
      (* When the theory has raised Unsat, add_boolean_conflict
         might 'forget' the initial conflict clause, and only add the
         analyzed backtrack clause. So in those case, we use add_clause
         to make sure the initial conflict clause is also added. *)
      if Clause.attached self.store confl then
        add_boolean_conflict self confl
      else
        add_clause_ ~pool:self.clauses_learnt self confl;
      Stat.incr self.n_conflicts;
      Event.emit self.on_conflict confl
    | None ->
      (* No Conflict *)
      assert (self.elt_head = AVec.size self.trail);
      assert (self.elt_head = self.th_head);
      if max_conflicts > 0 && !n_conflicts >= max_conflicts then (
        Profile.instant "sat.restart";
        Log.debug 1 "(sat.restarting)";
        cancel_until self 0;
        Stat.incr self.n_restarts;
        raise_notrace Restart
      );

      (* if decision_level() = 0 then simplify (); *)
      let do_gc =
        !(self.max_clauses_learnt) > 0
        && cp_size_ self.clauses_learnt - AVec.size self.trail
           > !(self.max_clauses_learnt)
        || Vec.exists cp_needs_gc_ self.clause_pools
      in
      if do_gc then (
        reduce_clause_db self;
        on_progress ()
      );

      let decided = pick_branch_lit ~full:true self in
      if not decided then raise_notrace E_sat
  done

let eval_level (self : t) (a : atom) =
  let lvl = Atom.level self.store a in
  if Atom.is_true self.store a then (
    assert (lvl >= 0);
    true, lvl
  ) else if Atom.is_false self.store a then
    false, lvl
  else
    raise UndecidedLit

let[@inline] eval st lit = fst @@ eval_level st lit

(* fixpoint of propagation and decisions until a model is found, or a
   conflict is reached *)
let solve_ ~on_progress (self : t) : unit =
  let@ () = Profile.with_ "sat.solve" in
  Log.debugf 5 (fun k ->
      k "(@[sat.solve :assms %d@])" (AVec.size self.assumptions));
  check_unsat_ self;
  try
    perform_delayed_actions self;
    (* add initial clauses *)
    let max_conflicts = ref (float_of_int restart_first) in
    let max_learnt =
      ref (float_of_int (nb_clauses self) *. learntsize_factor)
    in
    while true do
      on_progress ();
      try
        self.max_clauses_learnt := int_of_float !max_learnt;
        search self ~on_progress ~max_conflicts:(int_of_float !max_conflicts)
      with
      | Restart ->
        max_conflicts := !max_conflicts *. restart_inc;
        max_learnt := !max_learnt *. learntsize_inc
      | E_sat ->
        assert (
          self.elt_head = AVec.size self.trail
          && has_no_delayed_actions self
          && self.next_decisions = []);
        on_progress ();
        let (module P) = self.plugin in
        (match P.final_check (full_slice self) with
        | () ->
          if
            self.elt_head = AVec.size self.trail
            && has_no_delayed_actions self
            && self.next_decisions = []
          then
            (* nothing more to do, that means the plugin is satisfied
               with the trail *)
            raise_notrace E_sat;
          (* otherwise, keep on *)
          perform_delayed_actions self
        | exception Th_conflict c ->
          check_is_conflict_ self c;
          Clause.iter self.store c ~f:(fun a ->
              insert_var_order self (Atom.var a));

          Profile.instant "sat.th-conflict";
          Log.debugf 5 (fun k ->
              k "(@[sat.theory-conflict-clause@ %a@])" (Clause.debug self.store)
                c);
          Stat.incr self.n_conflicts;
          Event.emit self.on_conflict c;
          Delayed_actions.add_clause_learnt self.delayed_actions c;
          perform_delayed_actions self;
          on_progress ())
    done
  with E_sat -> ()

let assume self cnf : unit =
  List.iter
    (fun l ->
      let atoms = Util.array_of_list_map (make_atom_ self) l in
      let proof =
        Proof_trace.add_step self.proof @@ fun () ->
        Proof_sat.sat_input_clause l
      in
      let c = Clause.make_a self.store ~removable:false atoms proof in
      Log.debugf 10 (fun k ->
          k "(@[sat.assume-clause@ @[<hov 2>%a@]@])" (Clause.debug self.store) c);
      Delayed_actions.add_clause_learnt self.delayed_actions c)
    cnf

let[@inline] store st = st.store
let[@inline] proof st = st.proof

let[@inline] add_lit self ?default_pol lit =
  ignore (make_atom_ self lit ?default_pol : atom)

let[@inline] set_default_pol (self : t) (lit : Lit.t) (pol : bool) : unit =
  let a = make_atom_ self lit ~default_pol:pol in
  Var.set_default_pol self.store (Atom.var a) pol

(* Result type *)
type res = Sat of sat_state | Unsat of clause unsat_state

let pp_all self lvl status =
  Log.debugf lvl (fun k ->
      k
        "(@[<v>sat.full-state :res %s - Full summary:@,\
         @[<hov 2>Trail:@\n\
         %a@]@,\
         @[<hov 2>Hyps:@\n\
         %a@]@,\
         @[<hov 2>Lemmas:@\n\
         %a@]@,\
         @]@."
        status
        (AVec.pp @@ Atom.debug self.store)
        self.trail
        (CVec.pp @@ Clause.debug self.store)
        self.clauses_hyps
        (Util.pp_iter @@ Clause.debug self.store)
        (cp_to_iter_ self.clauses_learnt))

let mk_sat (self : t) : sat_state =
  pp_all self 99 "SAT";
  let t = self.trail in
  let module M = struct
    let iter_trail f = AVec.iter ~f:(fun a -> f (Atom.lit self.store a)) t
    let[@inline] eval f = eval self (make_atom_ self f)
    let[@inline] eval_level f = eval_level self (make_atom_ self f)
  end in
  (module M)

(* make a clause that contains no level-0 false literals, by resolving
   against them. This clause can be used in a refutation proof.
   Note that the clause might still contain some {b assumptions}. *)
let resolve_with_lvl0 (self : t) (c : clause) : clause =
  let lvl0 = ref [] in
  let res = ref [] in
  let to_unmark = self.temp_atom_vec in
  assert (AVec.is_empty to_unmark);

  (* resolve against the root cause of [a] being false *)
  let resolve_with_a (a : atom) : unit =
    assert (Atom.is_false self.store a && Atom.level self.store a = 0);
    if not (Var.marked self.store (Atom.var a)) then (
      Log.debugf 50 (fun k ->
          k "(@[sat.resolve-lvl0@ :atom %a@])" (Atom.debug self.store) a);
      AVec.push to_unmark a;
      Var.mark self.store (Atom.var a);

      let p = proof_of_atom_lvl0_ self (Atom.neg a) in
      lvl0 := p :: !lvl0
    )
  in

  Clause.iter self.store c ~f:(fun a ->
      if Atom.level self.store a = 0 then resolve_with_a a);
  AVec.iter to_unmark ~f:(fun a -> Var.unmark self.store (Atom.var a));
  AVec.clear to_unmark;

  if !lvl0 = [] then
    c
  (* no resolution happened *)
  else (
    let proof =
      Proof_trace.add_step self.proof @@ fun () ->
      let lits = List.rev_map (Atom.lit self.store) !res in
      let hyps = Iter.of_list (Clause.proof_step self.store c :: !lvl0) in
      Proof_sat.sat_redundant_clause lits ~hyps
    in
    Clause.make_l self.store ~removable:false !res proof
  )

let mk_unsat (self : t) (us : unsat_cause) : _ unsat_state =
  pp_all self 99 "UNSAT";
  let store = store self in
  let unsat_assumptions () =
    match us with
    | US_local { first = _; core } ->
      let lits = Iter.of_list core |> Iter.map (Atom.lit store) in
      lits
    | _ -> Iter.empty
  in
  let unsat_conflict =
    match us with
    | US_false c0 ->
      Log.debugf 10 (fun k ->
          k "(@[sat.unsat-conflict-clause@ %a@])" (Clause.debug store) c0);
      let c = resolve_with_lvl0 self c0 in
      Log.debugf 10 (fun k ->
          k "(@[sat.unsat-conflict-clause.proper@ %a@])" (Clause.debug store) c);
      fun () -> c
    | US_local { core = []; _ } -> assert false
    | US_local { first; core } ->
      (* TODO: do we need to filter out literals? *)
      let c =
        lazy
          (let core = List.rev core in
           (* increasing trail order *)
           assert (Atom.equal first @@ List.hd core);
           let proof =
             Proof_trace.add_step self.proof @@ fun () ->
             let lits = List.rev_map (Atom.lit self.store) core in
             Proof_sat.sat_unsat_core lits
           in
           Clause.make_l self.store ~removable:false [] proof)
      in
      fun () -> Lazy.force c
  in
  let module M = struct
    type clause = Clause.t

    let unsat_conflict = unsat_conflict
    let unsat_assumptions = unsat_assumptions

    let unsat_proof () =
      let c = unsat_conflict () in
      Clause.proof_step self.store c
  end in
  (module M)

type propagation_result =
  | PR_sat
  | PR_conflict of { backtracked: int }
  | PR_unsat of clause unsat_state

(* decide on assumptions, and do propagations, but no other kind of decision *)
let propagate_under_assumptions (self : t) : propagation_result =
  let result = ref PR_sat in
  try
    while true do
      match propagate self with
      | Some confl ->
        (* When the theory has raised Unsat, add_boolean_conflict
           might 'forget' the initial conflict clause, and only add the
           analyzed backtrack clause. So in those case, we use add_clause
           to make sure the initial conflict clause is also added. *)
        if Clause.attached self.store confl then
          add_boolean_conflict self confl
        else
          add_clause_ ~pool:self.clauses_learnt self confl;
        Stat.incr self.n_conflicts;

        (* see by how much we backtracked the decision trail *)
        let new_lvl = decision_level self in
        assert (new_lvl < AVec.size self.assumptions);
        let backtracked = AVec.size self.assumptions - new_lvl in
        result := PR_conflict { backtracked };
        AVec.shrink self.assumptions new_lvl;
        raise_notrace Exit
      | None ->
        (* No Conflict *)
        let decided = pick_branch_lit self ~full:false in
        if not decided then (
          result := PR_sat;
          raise Exit
        )
    done;
    assert false
  with Exit -> !result

let add_clause_atoms_ self ~pool ~removable (c : atom array)
    (pr : Proof_step.id) : unit =
  try
    let c = Clause.make_a self.store ~removable c pr in
    add_clause_ ~pool self c
  with E_unsat (US_false c) -> self.unsat_at_0 <- Some c

let add_clause_a self c pr : unit =
  let c = Array.map (make_atom_ self) c in
  add_clause_atoms_ ~pool:self.clauses_learnt ~removable:false self c pr

let add_clause self (c : Lit.t list) (pr : Proof_step.id) : unit =
  let c = Util.array_of_list_map (make_atom_ self) c in
  add_clause_atoms_ ~pool:self.clauses_learnt ~removable:false self c pr

let add_input_clause self (c : Lit.t list) =
  let pr =
    Proof_trace.add_step self.proof @@ fun () -> Proof_sat.sat_input_clause c
  in
  add_clause self c pr

let add_input_clause_a self c =
  let pr =
    Proof_trace.add_step self.proof @@ fun () ->
    Proof_sat.sat_input_clause (Array.to_list c)
  in
  add_clause_a self c pr

(* run [f()] with additional assumptions *)
let with_local_assumptions_ (self : t) (assumptions : Lit.t list) f =
  let old_assm_lvl = AVec.size self.assumptions in
  List.iter
    (fun lit ->
      let a = make_atom_ self lit in
      AVec.push self.assumptions a)
    assumptions;
  try
    let x = f () in
    AVec.shrink self.assumptions old_assm_lvl;
    x
  with e ->
    AVec.shrink self.assumptions old_assm_lvl;
    raise e

let solve ?(on_progress = fun _ -> ()) ?(assumptions = []) (self : t) : res =
  cancel_until self 0;
  (* make sure we are at level 0 *)
  with_local_assumptions_ self assumptions @@ fun () ->
  try
    solve_ ~on_progress self;
    Sat (mk_sat self)
  with E_unsat us -> Unsat (mk_unsat self us)

let push_assumption (self : t) (lit : Lit.t) : unit =
  let a = make_atom_ self lit in
  AVec.push self.assumptions a

let pop_assumptions self n : unit =
  let n_ass = AVec.size self.assumptions in
  assert (n <= n_ass);
  AVec.shrink self.assumptions (n_ass - n)

let check_sat_propagations_only ?(assumptions = []) (self : t) :
    propagation_result =
  cancel_until self 0;
  with_local_assumptions_ self assumptions @@ fun () ->
  try
    check_unsat_ self;
    perform_delayed_actions self;
    (* add initial clauses *)
    propagate_under_assumptions self
  with E_unsat us ->
    let us = mk_unsat self us in
    PR_unsat us

let true_at_level0 (self : t) (lit : Lit.t) : bool =
  match find_atom_ self lit with
  | None -> false
  | Some a ->
    (try
       let b, lev = eval_level self a in
       b && lev = 0
     with UndecidedLit -> false)

let[@inline] eval_lit self (lit : Lit.t) : lbool =
  match find_atom_ self lit with
  | Some a -> eval_atom_ self a
  | None -> L_undefined

let create ?(stat = Stat.global) ?(size = `Big) ~proof (p : plugin) : t =
  let store = Store.create ~size ~stat () in
  let max_clauses_learnt = ref 0 in
  let self = create_ ~max_clauses_learnt ~store ~proof ~stat p in
  self

let plugin_cdcl_t (module P : THEORY_CDCL_T) : (module PLUGIN) =
  (module struct
    include P

    let has_theory = true
  end)

let mk_plugin_cdcl_t ~push_level ~pop_levels ?(partial_check = ignore)
    ~final_check () : (module PLUGIN) =
  (module struct
    let push_level = push_level
    let pop_levels = pop_levels
    let partial_check = partial_check
    let final_check = final_check
    let has_theory = true
  end)

let plugin_pure_sat : plugin =
  (module struct
    let push_level () = ()
    let pop_levels _ = ()
    let partial_check _ = ()
    let final_check _ = ()
    let has_theory = false
  end)

let create_pure_sat ?stat ?size ~proof () : t =
  create ?stat ?size ~proof plugin_pure_sat
