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
  mutable on_partial_check: (t -> theory_actions -> lit Iter.t -> unit) list;
  mutable on_final_check: (t -> theory_actions -> lit Iter.t -> unit) list;
  mutable on_th_combination:
    (t -> theory_actions -> (term * value) Iter.t) list;
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
  recurse:(t -> E_node.t -> term) -> t -> E_node.t -> term option

and model_completion_hook = t -> add:(term -> term -> unit) -> unit

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

let on_th_combination self f =
  self.on_th_combination <- f :: self.on_th_combination

let on_preprocess self f = self.preprocess <- f :: self.preprocess

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
    let mk_lit ?sign t : Lit.t = Lit.atom ?sign t
    let add_lit ?default_pol lit : unit = delayed_add_lit self ?default_pol lit
    let add_clause c pr : unit = delayed_add_clause self ~keep:true c pr
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
        let lit = Lit.atom t in
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
  Lit.atom ~sign u, pr

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

let[@inline] mk_lit _ ?sign t : lit = Lit.atom ?sign t

let[@inline] add_lit self _acts ?default_pol lit =
  delayed_add_lit self ?default_pol lit

let add_lit_t self _acts ?sign t =
  let lit = Lit.atom ?sign t in
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

(*
    let cc_merge self _acts n1 n2 e = CC.merge (cc self) n1 n2 e

    let cc_merge_t self acts t1 t2 e =
      let cc_acts = mk_cc_acts_ self.proof acts in
      cc_merge self cc_acts (cc_add_term self t1) (cc_add_term self t2) e

    let cc_raise_conflict_expl self acts e =
      let cc_acts = mk_cc_acts_ self.proof acts in
      CC.raise_conflict_from_expl (cc self) cc_acts e
      *)

(** {2 Interface with the SAT solver} *)

let rec push_lvl_ = function
  | Ths_nil -> ()
  | Ths_cons r ->
    r.push_level r.st;
    push_lvl_ r.next

let rec pop_lvls_ n = function
  | Ths_nil -> ()
  | Ths_cons r ->
    r.pop_levels r.st n;
    pop_lvls_ n r.next

(** {2 Model construction and theory combination} *)

(* make model from the congruence closure *)
let mk_model_ (self : t) (lits : lit Iter.t) : Model.t =
  Log.debug 1 "(smt.solver.mk-model)";
  Profile.with_ "smt-solver.mk-model" @@ fun () ->
  let module M = Term.Tbl in
  let { cc; tst; model_ask = model_ask_hooks; model_complete; _ } = self in

  let model = M.create 128 in

  (* first, add all literals to the model using the given propositional model
     [lits]. *)
  lits (fun lit ->
      let t, sign = Lit.signed_term lit in
      M.replace model t (Term.bool_val tst sign));

  (* populate with information from the CC *)
  (* FIXME
     CC.get_model_for_each_class cc (fun (_, ts, v) ->
         Iter.iter
           (fun n ->
             let t = E_node.term n in
             M.replace model t v)
           ts);
  *)

  (* complete model with theory specific values *)
  let complete_with f =
    f self ~add:(fun t u ->
        if not (M.mem model t) then (
          Log.debugf 20 (fun k ->
              k "(@[smt.model-complete@ %a@ :with-val %a@])" Term.pp_debug t
                Term.pp_debug u);
          M.replace model t u
        ))
  in
  List.iter complete_with model_complete;

  (* compute a value for [n]. *)
  let rec val_for_class (n : E_node.t) : term =
    Log.debugf 5 (fun k -> k "val-for-term %a" E_node.pp n);
    let repr = CC.find cc n in
    Log.debugf 5 (fun k -> k "val-for-term.repr %a" E_node.pp repr);

    (* see if a value is found already (always the case if it's a boolean) *)
    match M.get model (E_node.term repr) with
    | Some t_val ->
      Log.debugf 5 (fun k -> k "cached val is %a" Term.pp_debug t_val);
      t_val
    | None ->
      (* try each model hook *)
      let rec try_hooks_ = function
        | [] -> E_node.term repr
        | h :: hooks ->
          (match h ~recurse:(fun _ n -> val_for_class n) self repr with
          | None -> try_hooks_ hooks
          | Some t -> t)
      in

      let t_val =
        try_hooks_ model_ask_hooks
        (* FIXME: the more complete version?
           match
             (* look for a value in the model for any term in the class *)
             E_node.iter_class repr
             |> Iter.find_map (fun n -> M.get model (E_node.term n))
           with
           | Some v -> v
           | None -> try_hooks_ model_ask_hooks
        *)
      in

      M.replace model (E_node.term repr) t_val;
      (* be sure to cache the value *)
      Log.debugf 5 (fun k -> k "val is %a" Term.pp_debug t_val);
      t_val
  in

  (* map terms of each CC class to the value computed for their class. *)
  CC.all_classes cc (fun repr ->
      let t_val = val_for_class repr in
      (* value for this class *)
      E_node.iter_class repr (fun u ->
          let t_u = E_node.term u in
          if (not (E_node.equal u repr)) && not (Term.equal t_u t_val) then
            M.replace model t_u t_val));
  Model.Internal_.of_tbl model

(* do theory combination using the congruence closure. Each theory
   can merge classes, *)
let check_th_combination_ (self : t) (_acts : theory_actions) lits :
    (Model.t, th_combination_conflict) result =
  (* FIXME

     (* enter model mode, disabling most of congruence closure *)
              CC.with_model_mode cc @@ fun () ->
              let set_val (t, v) : unit =
                Log.debugf 50 (fun k ->
                    k "(@[solver.th-comb.cc-set-term-value@ %a@ :val %a@])" Term.pp_debug t
                      Term.pp_debug v);
                CC.set_model_value cc t v
              in

           (* obtain assignments from the hook, and communicate them to the CC *)
           let add_th_values f : unit =
             let vals = f self acts in
             Iter.iter set_val vals
           in
        try
          List.iter add_th_values self.on_th_combination;
          CC.check cc;
          let m = mk_model_ self in
          Ok m
        with Semantic_conflict c -> Error c
  *)
  let m = mk_model_ self lits in
  Ok m

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
          A.propagate lit reason)
      acts
  | Error (CC.Result_action.Conflict (lits, pr)) -> A.raise_conflict lits pr

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
  (* transmit to CC *)
  let cc = cc self in

  if not final then CC.assert_lits cc lits;
  (* transmit to theories. *)
  check_cc_with_acts_ self acts;
  if final then (
    List.iter (fun f -> f self acts lits) self.on_final_check;
    check_cc_with_acts_ self acts;

    (match check_th_combination_ self acts lits with
    | Ok m -> self.last_model <- Some m
    | Error { lits; semantic } ->
      (* bad model, we add a clause to remove it *)
      Log.debugf 5 (fun k ->
          k "(@[solver.th-comb.conflict@ :lits (@[%a@])@ :same-val (@[%a@])@])"
            (Util.pp_list Lit.pp) lits
            (Util.pp_list @@ Fmt.Dump.(triple bool Term.pp_debug Term.pp_debug))
            semantic);

      let c1 = List.rev_map Lit.neg lits in
      let c2 =
        semantic
        |> List.rev_map (fun (sign, t, u) ->
               let eqn = Term.eq self.tst t u in
               let lit = Lit.atom ~sign:(not sign) eqn in
               (* make sure to consider the new lit *)
               add_lit self acts lit;
               lit)
      in

      let c = List.rev_append c1 c2 in
      let pr =
        Proof_trace.add_step self.proof @@ fun () -> Proof_core.lemma_cc c
      in

      Log.debugf 20 (fun k ->
          k "(@[solver.th-comb.add-semantic-conflict-clause@ %a@])"
            (Util.pp_list Lit.pp) c);
      (* will add a delayed action *)
      add_clause_temp self acts c pr);

    Perform_delayed_th.top self acts
  ) else (
    List.iter (fun f -> f self acts lits) self.on_partial_check;
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
  push_lvl_ self.th_states

let pop_levels self n : unit =
  self.last_model <- None;
  self.level <- self.level - n;
  CC.pop_levels (cc self) n;
  pop_lvls_ n self.th_states

let n_levels self = self.level

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
      on_th_combination = [];
      level = 0;
      complete = true;
    }
  in
  self
