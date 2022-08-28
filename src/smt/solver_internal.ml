open Sigs
module Ty = Term

type th_states =
  | Ths_nil
  | Ths_cons : {
      st: 'a;
      push_level: 'a -> unit;
      pop_levels: 'a -> int -> unit;
      next: th_states;
    }
      -> th_states

(* actions from the sat solver *)
type sat_acts = Sidekick_sat.acts
type theory_actions = sat_acts
type simplify_hook = Simplify.hook

module type PREPROCESS_ACTS = sig
  val proof : proof_trace
  val mk_lit : ?sign:bool -> term -> lit
  val add_clause : lit list -> step_id -> unit
  val add_lit : ?default_pol:bool -> lit -> unit
  val add_term_needing_combination : term -> unit
end

type preprocess_actions = (module PREPROCESS_ACTS)

module Registry = Registry

(* delayed actions. We avoid doing them on the spot because, when
   triggered by a theory, they might go back to the theory "too early". *)
type delayed_action =
  | DA_add_clause of { c: lit list; pr: step_id; keep: bool }
  | DA_add_lit of { default_pol: bool option; lit: lit }

type t = {
  tst: Term.store;  (** state for managing terms *)
  cc: CC.t;  (** congruence closure *)
  proof: proof_trace;  (** proof logger *)
  registry: Registry.t;
  on_progress: (unit, unit) Event.Emitter.t;
  th_comb: Th_combination.t;
  mutable on_partial_check: (t -> theory_actions -> lit Iter.t -> unit) list;
  mutable on_final_check: (t -> theory_actions -> lit Iter.t -> unit) list;
  mutable preprocess: preprocess_hook list;
  mutable model_ask: model_ask_hook list;
  mutable model_complete: model_completion_hook list;
  simp: Simplify.t;
  preprocessed: unit Term.Tbl.t;
  delayed_actions: delayed_action Queue.t;
  mutable last_model: Model.t option;
  mutable th_states: th_states;  (** Set of theories *)
  mutable level: int;
  mutable complete: bool;
  stat: Stat.t;
  count_axiom: int Stat.counter;
  count_preprocess_clause: int Stat.counter;
  count_conflict: int Stat.counter;
  count_propagate: int Stat.counter;
}

and preprocess_hook = t -> preprocess_actions -> term -> unit

and model_ask_hook =
  t -> Model_builder.t -> Term.t -> (value * Term.t list) option

and model_completion_hook = t -> add:(term -> value -> unit) -> unit

type solver = t

let[@inline] cc (self : t) = self.cc
let[@inline] tst self = self.tst
let[@inline] proof self = self.proof
let stats self = self.stat
let registry self = self.registry
let simplifier self = self.simp
let simplify_t self (t : Term.t) : _ option = Simplify.normalize self.simp t
let simp_t self (t : Term.t) : Term.t * _ = Simplify.normalize_t self.simp t
let add_simplifier (self : t) f : unit = Simplify.add_hook self.simp f

let[@inline] has_delayed_actions self =
  not (Queue.is_empty self.delayed_actions)

let on_preprocess self f = self.preprocess <- f :: self.preprocess

let add_term_needing_combination self t =
  Th_combination.add_term_needing_combination self.th_comb t

let on_model ?ask ?complete self =
  Option.iter (fun f -> self.model_ask <- f :: self.model_ask) ask;
  Option.iter
    (fun f -> self.model_complete <- f :: self.model_complete)
    complete;
  ()

let[@inline] raise_conflict self (acts : theory_actions) c proof : 'a =
  let (module A) = acts in
  Stat.incr self.count_conflict;
  A.raise_conflict c proof

let[@inline] propagate self (acts : theory_actions) p ~reason : unit =
  let (module A) = acts in
  Stat.incr self.count_propagate;
  A.propagate p (Sidekick_sat.Consequence reason)

let[@inline] propagate_l self acts p cs proof : unit =
  propagate self acts p ~reason:(fun () -> cs, proof)

let add_sat_clause_ self (acts : theory_actions) ~keep lits (proof : step_id) :
    unit =
  let (module A) = acts in
  Stat.incr self.count_axiom;
  A.add_clause ~keep lits proof

let add_sat_lit_ _self ?default_pol (acts : theory_actions) (lit : Lit.t) : unit
    =
  let (module A) = acts in
  A.add_lit ?default_pol lit

let delayed_add_lit (self : t) ?default_pol (lit : Lit.t) : unit =
  Queue.push (DA_add_lit { default_pol; lit }) self.delayed_actions

let delayed_add_clause (self : t) ~keep (c : Lit.t list) (pr : step_id) : unit =
  Queue.push (DA_add_clause { c; pr; keep }) self.delayed_actions

let preprocess_term_ (self : t) (t0 : term) : unit =
  let module A = struct
    let proof = self.proof
    let mk_lit ?sign t : Lit.t = Lit.atom ?sign self.tst t
    let add_lit ?default_pol lit : unit = delayed_add_lit self ?default_pol lit
    let add_clause c pr : unit = delayed_add_clause self ~keep:true c pr

    let add_term_needing_combination t =
      Th_combination.add_term_needing_combination self.th_comb t
  end in
  let acts = (module A : PREPROCESS_ACTS) in

  (* how to preprocess a term and its subterms *)
  let rec preproc_rec_ t =
    if not (Term.Tbl.mem self.preprocessed t) then (
      Term.Tbl.add self.preprocessed t ();

      (* process sub-terms first *)
      Term.iter_shallow t ~f:(fun _inb u -> preproc_rec_ u);

      Log.debugf 50 (fun k -> k "(@[smt.preprocess@ %a@])" Term.pp_debug t);

      (* signal boolean subterms, so as to decide them
         in the SAT solver *)
      if Ty.is_bool (Term.ty t) then (
        Log.debugf 5 (fun k ->
            k "(@[solver.map-bool-subterm-to-lit@ :subterm %a@])" Term.pp_debug
              t);

        (* make a literal *)
        let lit = Lit.atom self.tst t in
        (* ensure that SAT solver has a boolean atom for [u] *)
        delayed_add_lit self lit;

        (* also map [sub] to this atom in the congruence closure, for propagation *)
        let cc = cc self in
        CC.set_as_lit cc (CC.add_term cc t) lit
      );

      List.iter (fun f -> f self acts t) self.preprocess
    )
  in
  preproc_rec_ t0

(* simplify literal, then preprocess the result *)
let simplify_and_preproc_lit (self : t) (lit : Lit.t) : Lit.t * step_id option =
  let t = Lit.term lit in
  let sign = Lit.sign lit in
  let u, pr =
    match simplify_t self t with
    | None -> t, None
    | Some (u, pr_t_u) ->
      Log.debugf 30 (fun k ->
          k "(@[smt-solver.simplify@ :t %a@ :into %a@])" Term.pp_debug t
            Term.pp_debug u);
      u, Some pr_t_u
  in
  preprocess_term_ self u;
  Lit.atom ~sign self.tst u, pr

let push_decision (self : t) (acts : theory_actions) (lit : lit) : unit =
  let (module A) = acts in
  (* make sure the literal is preprocessed *)
  let lit, _ = simplify_and_preproc_lit self lit in
  let sign = Lit.sign lit in
  A.add_decision_lit (Lit.abs lit) sign

module type ARR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val to_list : 'a t -> 'a list
end

module Preprocess_clause (A : ARR) = struct
  (* preprocess a clause's literals, possibly emitting a proof
     for the preprocessing. *)
  let top (self : t) (c : lit A.t) (pr_c : step_id) : lit A.t * step_id =
    let steps = ref [] in

    (* simplify a literal, then preprocess it *)
    let[@inline] simp_lit lit =
      let lit, pr = simplify_and_preproc_lit self lit in
      Option.iter (fun pr -> steps := pr :: !steps) pr;
      lit
    in
    let c' = A.map simp_lit c in

    let pr_c' =
      if !steps = [] then
        pr_c
      else (
        Stat.incr self.count_preprocess_clause;
        Proof_trace.add_step self.proof @@ fun () ->
        Proof_core.lemma_rw_clause pr_c ~res:(A.to_list c') ~using:!steps
      )
    in
    c', pr_c'
end
[@@inline]

module PC_list = Preprocess_clause (struct
  type 'a t = 'a list

  let map = CCList.map
  let to_list l = l
end)

module PC_arr = Preprocess_clause (CCArray)

let preprocess_clause = PC_list.top
let preprocess_clause_array = PC_arr.top

module type PERFORM_ACTS = sig
  type t

  val add_clause : solver -> t -> keep:bool -> lit list -> step_id -> unit
  val add_lit : solver -> t -> ?default_pol:bool -> lit -> unit
end

module Perform_delayed (A : PERFORM_ACTS) = struct
  (* perform actions that were delayed *)
  let top (self : t) (acts : A.t) : unit =
    while not (Queue.is_empty self.delayed_actions) do
      let act = Queue.pop self.delayed_actions in
      match act with
      | DA_add_clause { c; pr = pr_c; keep } ->
        let c', pr_c' = preprocess_clause self c pr_c in
        A.add_clause self acts ~keep c' pr_c'
      | DA_add_lit { default_pol; lit } ->
        preprocess_term_ self (Lit.term lit);
        A.add_lit self acts ?default_pol lit
    done
end
[@@inline]

module Perform_delayed_th = Perform_delayed (struct
  type t = theory_actions

  let add_clause self acts ~keep c pr : unit =
    add_sat_clause_ self acts ~keep c pr

  let add_lit self acts ?default_pol lit : unit =
    add_sat_lit_ self acts ?default_pol lit
end)

let[@inline] add_clause_temp self _acts c (proof : step_id) : unit =
  let c, proof = preprocess_clause self c proof in
  delayed_add_clause self ~keep:false c proof

let[@inline] add_clause_permanent self _acts c (proof : step_id) : unit =
  let c, proof = preprocess_clause self c proof in
  delayed_add_clause self ~keep:true c proof

let[@inline] mk_lit self ?sign t : lit = Lit.atom ?sign self.tst t

let[@inline] add_lit self _acts ?default_pol lit =
  delayed_add_lit self ?default_pol lit

let add_lit_t self _acts ?sign t =
  let lit = Lit.atom ?sign self.tst t in
  let lit, _ = simplify_and_preproc_lit self lit in
  delayed_add_lit self lit

let on_final_check self f = self.on_final_check <- f :: self.on_final_check

let on_partial_check self f =
  self.on_partial_check <- f :: self.on_partial_check

let on_progress self = Event.of_emitter self.on_progress
let on_cc_new_term self f = Event.on (CC.on_new_term (cc self)) ~f
let on_cc_pre_merge self f = Event.on (CC.on_pre_merge (cc self)) ~f
let on_cc_post_merge self f = Event.on (CC.on_post_merge (cc self)) ~f
let on_cc_conflict self f = Event.on (CC.on_conflict (cc self)) ~f
let on_cc_propagate self f = Event.on (CC.on_propagate (cc self)) ~f
let on_cc_is_subterm self f = Event.on (CC.on_is_subterm (cc self)) ~f
let cc_add_term self t = CC.add_term (cc self) t
let cc_mem_term self t = CC.mem_term (cc self) t
let cc_find self n = CC.find (cc self) n
let is_complete self = self.complete
let last_model self = self.last_model

let cc_are_equal self t1 t2 =
  let n1 = cc_add_term self t1 in
  let n2 = cc_add_term self t2 in
  E_node.equal (cc_find self n1) (cc_find self n2)

let cc_resolve_expl self e : lit list * _ =
  let r = CC.explain_expl (cc self) e in
  r.lits, r.pr self.proof

(** {2 Interface with the SAT solver} *)

let rec push_lvl_theories_ = function
  | Ths_nil -> ()
  | Ths_cons r ->
    r.push_level r.st;
    push_lvl_theories_ r.next

let rec pop_lvls_theories_ n = function
  | Ths_nil -> ()
  | Ths_cons r ->
    r.pop_levels r.st n;
    pop_lvls_theories_ n r.next

(** {2 Model construction and theory combination} *)

(* make model from the congruence closure *)
let mk_model_ (self : t) (lits : lit Iter.t) : Model.t =
  let@ () = Profile.with_ "smt-solver.mk-model" in
  Log.debug 1 "(smt.solver.mk-model)";
  let module MB = Model_builder in
  let { cc; tst; model_ask = model_ask_hooks; model_complete; _ } = self in

  let model = Model_builder.create tst in

  (* first, add all literals to the model using the given propositional model
     induced by the trail [lits]. *)
  lits (fun lit ->
      let t, sign = Lit.signed_term lit in
      MB.add model t (Term.bool_val tst sign));

  (* complete model with theory specific values using the completion hooks.
     This generally adds values that theories already explicitly have
     computed in their theory-specific models, e.g. in the simplexe. *)
  let complete_with f =
    f self ~add:(fun t v ->
        if not (MB.mem model t) then (
          Log.debugf 20 (fun k ->
              k "(@[smt.model-complete@ %a@ :with-val %a@])" Term.pp t Term.pp v);
          MB.add model t v
        ))
  in
  List.iter complete_with model_complete;

  (* require a value for each class that doesn't already have one *)
  CC.all_classes cc (fun repr ->
      let t = E_node.term repr in
      MB.require_eval model t);

  (* now for the fixpoint. This is typically where composite theories such
     as arrays and datatypes contribute their skeleton values. *)
  let rec compute_fixpoint () =
    match MB.pop_required model with
    | None -> ()
    | Some t ->
      (* compute a value for [t] *)
      Log.debugf 5 (fun k ->
          k "(@[model.fixpoint.compute-for-required@ %a@])" Term.pp t);

      (* try each model hook *)
      let rec try_hooks_ = function
        | [] ->
          let c = MB.gensym model ~pre:"@c" ~ty:(Term.ty t) in
          Log.debugf 10 (fun k ->
              k "(@[model.fixpoint.pick-default-val@ %a@ :for %a@])" Term.pp c
                Term.pp t);
          MB.add model t c
        | h :: hooks ->
          (match h self model t with
          | None -> try_hooks_ hooks
          | Some (v, subs) ->
            MB.add model ~subs t v;
            ())
      in

      try_hooks_ model_ask_hooks;
      (* continue to next value *)
      (compute_fixpoint [@tailcall]) ()
  in

  compute_fixpoint ();
  MB.to_model model

(* do theory combination using the congruence closure. Each theory
   can merge classes, *)
let check_th_combination_ (self : t) (acts : theory_actions) _lits : unit =
  let lits_to_decide = Th_combination.pop_new_lits self.th_comb in
  if lits_to_decide <> [] then (
    let (module A) = acts in
    List.iter (fun lit -> A.add_lit ~default_pol:false lit) lits_to_decide
  )

(* call congruence closure, perform the actions it scheduled *)
let check_cc_with_acts_ (self : t) (acts : theory_actions) =
  let (module A) = acts in
  let cc = cc self in
  match CC.check cc with
  | Ok acts ->
    List.iter
      (function
        | CC.Result_action.Act_propagate { lit; reason } ->
          let reason = Sidekick_sat.Consequence reason in
          Stat.incr self.count_propagate;
          A.propagate lit reason)
      acts
  | Error (CC.Result_action.Conflict (lits, pr)) ->
    Stat.incr self.count_conflict;
    A.raise_conflict lits pr

(* handle a literal assumed by the SAT solver *)
let assert_lits_ ~final (self : t) (acts : theory_actions) (lits : Lit.t Iter.t)
    : unit =
  Log.debugf 2 (fun k ->
      k "(@[<hv1>@{<green>smt-solver.assume_lits@}%s[lvl=%d]@ %a@])"
        (if final then
          "[final]"
        else
          "")
        self.level
        (Util.pp_iter ~sep:"; " Lit.pp)
        lits);
  let cc = cc self in

  (* transmit to CC *)
  if not final then CC.assert_lits cc lits;
  check_cc_with_acts_ self acts;

  if final then (
    Perform_delayed_th.top self acts;

    (* transmit to theories. *)
    List.iter (fun f -> f self acts lits) self.on_final_check;
    check_cc_with_acts_ self acts;

    let new_work = has_delayed_actions self in

    (* do actual theory combination if nothing changed by pure "final check" *)
    if not new_work then (
      check_th_combination_ self acts lits;

      (* if theory combination didn't add new clauses, compute a model *)
      if not (has_delayed_actions self) then (
        let m = mk_model_ self lits in
        self.last_model <- Some m
      )
    );

    Perform_delayed_th.top self acts
  ) else (
    (* partial check *)
    List.iter (fun f -> f self acts lits) self.on_partial_check;
    (* re-check CC after theory actions, which might have merged classes *)
    check_cc_with_acts_ self acts;
    Perform_delayed_th.top self acts
  );
  ()

let[@inline] iter_atoms_ (acts : theory_actions) : _ Iter.t =
 fun f ->
  let (module A) = acts in
  A.iter_assumptions f

(* propagation from the bool solver *)
let check_ ~final (self : t) (acts : sat_acts) =
  let pb =
    if final then
      Profile.begin_ "solver.final-check"
    else
      Profile.null_probe
  in
  let iter = iter_atoms_ acts in
  Log.debugf 5 (fun k -> k "(smt-solver.assume :len %d)" (Iter.length iter));
  Event.emit self.on_progress ();
  assert_lits_ ~final self acts iter;
  Profile.exit pb

(* propagation from the bool solver *)
let[@inline] partial_check (self : t) (acts : Sidekick_sat.acts) : unit =
  check_ ~final:false self acts

(* perform final check of the model *)
let[@inline] final_check (self : t) (acts : Sidekick_sat.acts) : unit =
  check_ ~final:true self acts

let push_level self : unit =
  self.level <- 1 + self.level;
  CC.push_level (cc self);
  push_lvl_theories_ self.th_states

let pop_levels self n : unit =
  self.last_model <- None;
  self.level <- self.level - n;
  CC.pop_levels (cc self) n;
  pop_lvls_theories_ n self.th_states

let[@inline] n_levels self = self.level

let to_sat_plugin (self : t) : (module Sidekick_sat.PLUGIN) =
  (module struct
    let has_theory = true
    let push_level () = push_level self
    let pop_levels n = pop_levels self n
    let partial_check acts = partial_check self acts
    let final_check acts = final_check self acts
  end)

let declare_pb_is_incomplete self =
  if self.complete then Log.debug 1 "(solver.declare-pb-is-incomplete)";
  self.complete <- false

let add_theory_state ~st ~push_level ~pop_levels (self : t) =
  assert (self.level = 0);
  self.th_states <-
    Ths_cons { st; push_level; pop_levels; next = self.th_states }

let create (module A : ARG) ~stat ~proof (tst : Term.store) () : t =
  let self =
    {
      tst;
      cc = CC.create (module A : CC.ARG) ~size:`Big tst proof;
      proof;
      th_states = Ths_nil;
      stat;
      simp = Simplify.create tst ~proof;
      last_model = None;
      th_comb = Th_combination.create ~stat tst;
      on_progress = Event.Emitter.create ();
      preprocess = [];
      model_ask = [];
      model_complete = [];
      registry = Registry.create ();
      preprocessed = Term.Tbl.create 32;
      delayed_actions = Queue.create ();
      count_axiom = Stat.mk_int stat "smt.solver.th-axioms";
      count_preprocess_clause = Stat.mk_int stat "smt.solver.preprocess-clause";
      count_propagate = Stat.mk_int stat "smt.solver.th-propagations";
      count_conflict = Stat.mk_int stat "smt.solver.th-conflicts";
      on_partial_check = [];
      on_final_check = [];
      level = 0;
      complete = true;
    }
  in
  self
