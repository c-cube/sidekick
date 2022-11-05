open Sidekick_core
module Proof = Sidekick_proof
module Check_res = Sidekick_abstract_solver.Check_res
module Unknown = Sidekick_abstract_solver.Unknown

(** Argument to the solver *)
module type ARG = sig
  val or_l : Term.store -> Term.t list -> Term.t
  (** build a disjunction *)
end

(* TODO: embed a simplifier, and have simplify hooks in plugins.
    Then use the simplifier on any asserted term *)

type pending_assignment = {
  var: TVar.t;
  value: Value.t;
  level: int;
  reason: Reason.t;
}

type t = {
  tst: Term.store;
  vst: TVar.store;
  arg: (module ARG);
  stats: Stat.t;
  trail: Trail.t;
  plugins: plugin Vec.t;
  term_to_var: Term_to_var.t;
  pending_assignments: pending_assignment Vec.t;
  mutable last_res: Check_res.t option;
  proof_tracer: Proof.Tracer.t;
  n_conflicts: int Stat.counter;
  n_propagations: int Stat.counter;
  n_restarts: int Stat.counter;
}

and plugin_action = t

(* FIXME:
   - add [on_add_var: TVar.t -> unit]
     and [on_remove_var: TVar.t -> unit].
     these are called when a variable becomes relevant/is removed or GC'd
       (in particular: setup watches + var constraints on add,
        kill watches and remove constraints on remove)

   - add [gc_mark : TVar.t -> recurse:(TVar.t -> unit) -> unit]
     to mark sub-variables during GC mark phase.
*)
and plugin =
  | P : {
      st: 'st;
      name: string;
      push_level: 'st -> unit;
      pop_levels: 'st -> int -> unit;
      decide: 'st -> TVar.t -> Value.t option;
      propagate: 'st -> plugin_action -> TVar.t -> Value.t -> unit;
      term_to_var_hooks: 'st -> Term_to_var.hook list;
    }
      -> plugin

let create ?(stats = Stat.create ()) ~arg tst vst ~proof_tracer () : t =
  {
    tst;
    vst;
    arg;
    stats;
    trail = Trail.create ();
    plugins = Vec.create ();
    pending_assignments = Vec.create ();
    term_to_var = Term_to_var.create vst;
    last_res = None;
    proof_tracer;
    n_restarts = Stat.mk_int stats "cdsat.restarts";
    n_conflicts = Stat.mk_int stats "cdsat.conflicts";
    n_propagations = Stat.mk_int stats "cdsat.propagations";
  }

let[@inline] trail self = self.trail
let[@inline] iter_plugins self ~f = Vec.iter ~f self.plugins
let[@inline] tst self = self.tst
let[@inline] vst self = self.vst
let[@inline] last_res self = self.last_res

(* plugins *)

module Plugin = struct
  type t = plugin
  type builder = TVar.store -> t

  let[@inline] name (P p) = p.name

  let make_builder ~name ~create ~push_level ~pop_levels ~decide ~propagate
      ~term_to_var_hooks () : builder =
   fun vst ->
    let st = create vst in
    P { name; st; push_level; pop_levels; decide; propagate; term_to_var_hooks }
end

(* backtracking *)

let n_levels (self : t) : int = Trail.n_levels self.trail

let push_level (self : t) : unit =
  Log.debugf 50 (fun k -> k "(@[cdsat.core.push-level@])");
  Trail.push_level self.trail;
  Vec.iter self.plugins ~f:(fun (P p) -> p.push_level p.st);
  ()

let pop_levels (self : t) n : unit =
  let {
    tst = _;
    vst = _;
    arg = _;
    stats = _;
    trail;
    plugins;
    term_to_var = _;
    pending_assignments;
    last_res = _;
    proof_tracer = _;
    n_propagations = _;
    n_conflicts = _;
    n_restarts = _;
  } =
    self
  in
  Log.debugf 50 (fun k -> k "(@[cdsat.core.pop-levels %d@])" n);
  if n > 0 then (
    self.last_res <- None;
    Vec.clear pending_assignments
  );
  Trail.pop_levels trail n ~f:(fun v -> TVar.unassign self.vst v);
  Vec.iter plugins ~f:(fun (P p) -> p.pop_levels p.st n);
  ()

(* term to var *)

let[@inline] get_term_to_var self = self.term_to_var

let[@inline] term_to_var self t : TVar.t =
  Term_to_var.convert self.term_to_var t

let add_term_to_var_hook self h = Term_to_var.add_hook self.term_to_var h

(* plugins *)

let add_plugin self (pb : Plugin.builder) : unit =
  let (P p as plugin) = pb self.vst in
  Vec.push self.plugins plugin;
  List.iter (add_term_to_var_hook self) (p.term_to_var_hooks p.st)

(* solving *)

let add_ty (_self : t) ~ty:_ : unit = ()

(* Assign [v <- value] for [reason] at [level].
   This assignment is delayed. *)
let assign (self : t) (v : TVar.t) ~(value : Value.t) ~level:v_level ~reason :
    unit =
  Log.debugf 50 (fun k ->
      k "(@[cdsat.core.assign@ `%a`@ @[<- %a@]@ :reason %a@])"
        (TVar.pp self.vst) v Value.pp value Reason.pp reason);
  self.last_res <- None;
  Vec.push self.pending_assignments { var = v; value; level = v_level; reason }

exception E_conflict of Conflict.t

let raise_conflict (c : Conflict.t) : 'a = raise (E_conflict c)

(* add pending assignments to the trail. This might trigger a conflict
   in case an assignment contradicts an already existing assignment. *)
let perform_pending_assignments (self : t) : unit =
  while not (Vec.is_empty self.pending_assignments) do
    let { var = v; level = v_level; value; reason } =
      Vec.pop_exn self.pending_assignments
    in
    match TVar.value self.vst v with
    | None ->
      TVar.assign self.vst v ~value ~level:v_level ~reason;
      Trail.push_assignment self.trail v
    | Some value' when Value.equal value value' -> () (* idempotent *)
    | Some _value' ->
      (* conflict should only occur on booleans since they're the only
         propagation-able variables *)
      assert (Term.is_a_bool (TVar.term self.vst v));
      Log.debugf 0 (fun k ->
          k "TODO: conflict (incompatible values for %a)" (TVar.pp self.vst) v);
      raise_conflict
      @@ Conflict.make self.vst ~lit:(TLit.make true v) ~propagate_reason:reason
           ()
  done

let propagate (self : t) : Conflict.t option =
  let@ () = Profile.with_ "cdsat.propagate" in
  try
    let continue = ref true in
    while !continue do
      perform_pending_assignments self;

      while Trail.head self.trail < Trail.size self.trail do
        let var = Trail.get self.trail (Trail.head self.trail) in

        (* TODO: call plugins *)
        Log.debugf 0 (fun k -> k "TODO: propagate %a" (TVar.pp self.vst) var);

        let value =
          match TVar.value self.vst var with
          | Some v -> v
          | None -> assert false
        in

        iter_plugins self ~f:(fun (P p) -> p.propagate p.st self var value);

        (* move to next var *)
        Trail.set_head self.trail (Trail.head self.trail + 1)
      done;

      (* did we reach fixpoint? *)
      if Vec.is_empty self.pending_assignments then continue := false
    done;
    None
  with E_conflict c -> Some c

let solve ~on_exit ~on_progress ~should_stop ~assumptions (self : t) :
    Check_res.t =
  let@ () = Profile.with_ "cdsat.solve" in
  self.last_res <- None;

  (* FIXME: handle assumptions.
     - do assumptions first when deciding (forced decisions)
     - in case of conflict below assumptions len, special conflict analysis to
       compute unsat core
  *)

  (* control if loop stops *)
  let continue = ref true in
  let n_conflicts = ref 0 in
  let res = ref (Check_res.Unknown Unknown.U_incomplete) in

  (* main loop *)
  while !continue do
    if !n_conflicts mod 64 = 0 then on_progress ();

    (* propagate *)
    (match propagate self with
    | Some c ->
      Log.debugf 1 (fun k ->
          k "(@[cdsat.propagate.found-conflict@ %a@])" Conflict.pp c);
      incr n_conflicts;
      Stat.incr self.n_conflicts;

      (* TODO: handle conflict, learn a clause or declare unsat *)
      (* TODO: see if we want to restart *)
      assert false
    | None ->
      Log.debugf 0 (fun k -> k "TODO: decide");
      (* TODO: decide *)
      ());

    (* regularly check if it's time to stop *)
    if !n_conflicts mod 64 = 0 then
      if should_stop !n_conflicts then (
        Log.debugf 1 (fun k -> k "(@[cdsat.stop@ :caused-by-callback@])");

        res := Check_res.Unknown Unknown.U_asked_to_stop;
        continue := false
      )
  done;

  (* cleanup and exit *)
  List.iter (fun f -> f ()) on_exit;
  !res

(* plugin actions *)

module Plugin_action = struct
  type t = plugin_action

  let[@inline] propagate (self : t) var value reason : unit =
    assign self var ~value ~level:(Reason.level reason) ~reason

  let term_to_var = term_to_var
end
