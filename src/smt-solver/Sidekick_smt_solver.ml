(** Core of the SMT solver using Sidekick_sat

    Sidekick_sat (in src/sat/) is a modular SAT solver in
    pure OCaml.

    This builds a {!Sidekick_core.SOLVER} on top of it.
*)

(** Argument to pass to the functor {!Make} in order to create a
    new Msat-based SMT solver. *)
module type ARG = sig
  open Sidekick_core
  module T : TERM
  module Lit : LIT with module T = T

  type proof
  type proof_step

  module P :
    PROOF
      with type term = T.Term.t
       and type t = proof
       and type proof_step = proof_step
       and type lit = Lit.t

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t

  val mk_eq : T.Term.store -> T.Term.t -> T.Term.t -> T.Term.t
  (** [mk_eq store t u] builds the term [t=u] *)

  val is_valid_literal : T.Term.t -> bool
  (** Is this a valid boolean literal? (e.g. is it a closed term, not inside
      a quantifier) *)
end

module type S = Sidekick_core.SOLVER

module Registry : Sidekick_core.REGISTRY = struct
  (* registry keys *)
  module type KEY = sig
    type elt

    val id : int

    exception E of elt
  end

  type 'a key = (module KEY with type elt = 'a)
  type t = { tbl: exn Util.Int_tbl.t } [@@unboxed]

  let create () : t = { tbl = Util.Int_tbl.create 8 }
  let n_ = ref 0

  let create_key (type a) () : a key =
    let id = !n_ in
    incr n_;
    let module K = struct
      type elt = a

      exception E of a

      let id = id
    end in
    (module K)

  let get (type a) (self : t) (k : a key) : _ option =
    let (module K : KEY with type elt = a) = k in
    match Util.Int_tbl.get self.tbl K.id with
    | Some (K.E x) -> Some x
    | _ -> None

  let set (type a) (self : t) (k : a key) (v : a) : unit =
    let (module K) = k in
    Util.Int_tbl.replace self.tbl K.id (K.E v)
end

(** Main functor to get a solver. *)
module Make (A : ARG) :
  S
    with module T = A.T
     and type proof = A.proof
     and type proof_step = A.proof_step
     and module Lit = A.Lit
     and module P = A.P = struct
  module T = A.T
  module P = A.P
  module Ty = T.Ty
  module Term = T.Term
  module Lit = A.Lit

  type term = Term.t
  type ty = Ty.t
  type proof = A.proof
  type proof_step = A.proof_step
  type lit = Lit.t

  (* actions from the sat solver *)
  type sat_acts = (lit, proof, proof_step) Sidekick_sat.acts

  type th_combination_conflict = {
    lits: lit list;
    semantic: (bool * term * term) list;
        (* set of semantic eqns/diseqns (ie true only in current model) *)
  }
  (** Conflict obtained during theory combination. It involves equalities
      merged because of the current model so it's not a "true" conflict
      and doesn't need to kill the current trail. *)

  exception Semantic_conflict of th_combination_conflict

  (* the full argument to the congruence closure *)
  module CC_actions = struct
    module T = T
    module P = P
    module Lit = Lit

    type nonrec proof = proof
    type nonrec proof_step = proof_step

    let cc_view = A.cc_view

    let[@inline] mk_lit_eq ?sign store t u =
      A.Lit.atom ?sign store (A.mk_eq store t u)

    module Actions = struct
      module T = T
      module P = P
      module Lit = Lit

      type nonrec proof = proof
      type nonrec proof_step = proof_step
      type t = sat_acts

      let[@inline] proof (a : t) =
        let (module A) = a in
        A.proof

      let[@inline] raise_conflict (a : t) lits (pr : proof_step) =
        let (module A) = a in
        A.raise_conflict lits pr

      let[@inline] raise_semantic_conflict (_ : t) lits semantic =
        raise (Semantic_conflict { lits; semantic })

      let[@inline] propagate (a : t) lit ~reason =
        let (module A) = a in
        let reason = Sidekick_sat.Consequence reason in
        A.propagate lit reason
    end
  end

  module CC = Sidekick_cc.Make (CC_actions)
  module N = CC.N

  module Model = struct
    type t = Empty | Map of term Term.Tbl.t

    let empty = Empty

    let mem = function
      | Empty -> fun _ -> false
      | Map tbl -> Term.Tbl.mem tbl

    let find = function
      | Empty -> fun _ -> None
      | Map tbl -> Term.Tbl.get tbl

    let eval = find

    let pp out = function
      | Empty -> Fmt.string out "(model)"
      | Map tbl ->
        let pp_pair out (t, v) =
          Fmt.fprintf out "(@[<1>%a@ := %a@])" Term.pp t Term.pp v
        in
        Fmt.fprintf out "(@[<hv>model@ %a@])" (Util.pp_iter pp_pair)
          (Term.Tbl.to_iter tbl)
  end

  (* delayed actions. We avoid doing them on the spot because, when
     triggered by a theory, they might go back to the theory "too early". *)
  type delayed_action =
    | DA_add_clause of { c: lit list; pr: proof_step; keep: bool }
    | DA_add_lit of { default_pol: bool option; lit: lit }

  (** Internal solver, given to theories and to Msat *)
  module Solver_internal = struct
    module T = T
    module P = P
    module Lit = Lit
    module CC = CC
    module N = CC.N

    type nonrec proof = proof
    type nonrec proof_step = proof_step
    type term = Term.t
    type value = term
    type ty = Ty.t
    type lit = Lit.t
    type term_store = Term.store
    type clause_pool
    type ty_store = Ty.store

    type th_states =
      | Ths_nil
      | Ths_cons : {
          st: 'a;
          push_level: 'a -> unit;
          pop_levels: 'a -> int -> unit;
          next: th_states;
        }
          -> th_states

    type theory_actions = sat_acts

    module Simplify = struct
      type t = {
        tst: term_store;
        ty_st: ty_store;
        proof: proof;
        mutable hooks: hook list;
        (* store [t --> u by proof_steps] in the cache.
           We use a bag for the proof steps because it gives us structural
           sharing of subproofs. *)
        cache: (Term.t * proof_step Bag.t) Term.Tbl.t;
      }

      and hook = t -> term -> (term * proof_step Iter.t) option

      let create tst ty_st ~proof : t =
        { tst; ty_st; proof; hooks = []; cache = Term.Tbl.create 32 }

      let[@inline] tst self = self.tst
      let[@inline] ty_st self = self.ty_st
      let[@inline] proof self = self.proof
      let add_hook self f = self.hooks <- f :: self.hooks
      let clear self = Term.Tbl.clear self.cache

      let normalize (self : t) (t : Term.t) : (Term.t * proof_step) option =
        (* compute and cache normal form of [t] *)
        let rec loop t : Term.t * _ Bag.t =
          match Term.Tbl.find self.cache t with
          | res -> res
          | exception Not_found ->
            let steps_u = ref Bag.empty in
            let u = aux_rec ~steps:steps_u t self.hooks in
            Term.Tbl.add self.cache t (u, !steps_u);
            u, !steps_u
        and loop_add ~steps t =
          let u, pr_u = loop t in
          steps := Bag.append !steps pr_u;
          u
        (* try each function in [hooks] successively, and rewrite subterms *)
        and aux_rec ~steps t hooks : Term.t =
          match hooks with
          | [] ->
            let u = Term.map_shallow self.tst (loop_add ~steps) t in
            if Term.equal t u then
              t
            else
              loop_add ~steps u
          | h :: hooks_tl ->
            (match h self t with
            | None -> aux_rec ~steps t hooks_tl
            | Some (u, _) when Term.equal t u -> aux_rec ~steps t hooks_tl
            | Some (u, pr_u) ->
              let bag_u = Bag.of_iter pr_u in
              steps := Bag.append !steps bag_u;
              let v, pr_v = loop u in
              (* fixpoint *)
              steps := Bag.append !steps pr_v;
              v)
        in
        let u, pr_u = loop t in
        if Term.equal t u then
          None
        else (
          (* proof: [sub_proofs |- t=u] by CC + subproof *)
          let step =
            P.lemma_preprocess t u ~using:(Bag.to_iter pr_u) self.proof
          in
          Some (u, step)
        )

      let normalize_t self t =
        match normalize self t with
        | Some (u, pr_u) -> u, Some pr_u
        | None -> t, None
    end

    type simplify_hook = Simplify.hook

    module type PREPROCESS_ACTS = sig
      val proof : proof
      val mk_lit : ?sign:bool -> term -> lit
      val add_clause : lit list -> proof_step -> unit
      val add_lit : ?default_pol:bool -> lit -> unit
    end

    type preprocess_actions = (module PREPROCESS_ACTS)

    module Registry = Registry

    type t = {
      tst: Term.store;  (** state for managing terms *)
      ty_st: Ty.store;
      cc: CC.t lazy_t;  (** congruence closure *)
      proof: proof;  (** proof logger *)
      registry: Registry.t;
      mutable on_progress: unit -> unit;
      mutable on_partial_check:
        (t -> theory_actions -> lit Iter.t -> unit) list;
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
      recurse:(t -> CC.N.t -> term) -> t -> CC.N.t -> term option

    and model_completion_hook = t -> add:(term -> term -> unit) -> unit

    type solver = t

    module Proof = P

    let[@inline] cc (t : t) = Lazy.force t.cc
    let[@inline] tst t = t.tst
    let[@inline] ty_st t = t.ty_st
    let[@inline] proof self = self.proof
    let stats t = t.stat

    let[@inline] has_delayed_actions self =
      not (Queue.is_empty self.delayed_actions)

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

    let add_sat_clause_ self (acts : theory_actions) ~keep lits
        (proof : proof_step) : unit =
      let (module A) = acts in
      Stat.incr self.count_axiom;
      A.add_clause ~keep lits proof

    let add_sat_lit_ _self ?default_pol (acts : theory_actions) (lit : Lit.t) :
        unit =
      let (module A) = acts in
      A.add_lit ?default_pol lit

    let delayed_add_lit (self : t) ?default_pol (lit : Lit.t) : unit =
      Queue.push (DA_add_lit { default_pol; lit }) self.delayed_actions

    let delayed_add_clause (self : t) ~keep (c : Lit.t list) (pr : proof_step) :
        unit =
      Queue.push (DA_add_clause { c; pr; keep }) self.delayed_actions

    (* preprocess a term. We assume the term has been simplified already. *)
    let preprocess_term_ (self : t) (t0 : term) : unit =
      let module A = struct
        let proof = self.proof
        let mk_lit ?sign t : Lit.t = Lit.atom self.tst ?sign t

        let add_lit ?default_pol lit : unit =
          delayed_add_lit self ?default_pol lit

        let add_clause c pr : unit = delayed_add_clause self ~keep:true c pr
      end in
      let acts = (module A : PREPROCESS_ACTS) in

      (* how to preprocess a term and its subterms *)
      let rec preproc_rec_ t =
        if not (Term.Tbl.mem self.preprocessed t) then (
          Term.Tbl.add self.preprocessed t ();

          (* process sub-terms first *)
          Term.iter_shallow self.tst preproc_rec_ t;

          Log.debugf 50 (fun k -> k "(@[smt.preprocess@ %a@])" Term.pp t);

          (* signal boolean subterms, so as to decide them
             in the SAT solver *)
          if Ty.is_bool (Term.ty t) then (
            Log.debugf 5 (fun k ->
                k "(@[solver.map-bool-subterm-to-lit@ :subterm %a@])" Term.pp t);

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
    let simplify_and_preproc_lit_ (self : t) (lit : Lit.t) :
        Lit.t * proof_step option =
      let t = Lit.term lit in
      let sign = Lit.sign lit in
      let u, pr =
        match simplify_t self t with
        | None -> t, None
        | Some (u, pr_t_u) ->
          Log.debugf 30 (fun k ->
              k "(@[smt-solver.simplify@ :t %a@ :into %a@])" Term.pp t Term.pp u);
          u, Some pr_t_u
      in
      preprocess_term_ self u;
      Lit.atom self.tst ~sign u, pr

    let push_decision (self : t) (acts : theory_actions) (lit : lit) : unit =
      let (module A) = acts in
      (* make sure the literal is preprocessed *)
      let lit, _ = simplify_and_preproc_lit_ self lit in
      let sign = Lit.sign lit in
      A.add_decision_lit (Lit.abs lit) sign

    module type ARR = sig
      type 'a t

      val map : ('a -> 'b) -> 'a t -> 'b t
      val to_iter : 'a t -> 'a Iter.t
    end

    module Preprocess_clause (A : ARR) = struct
      (* preprocess a clause's literals, possibly emitting a proof
         for the preprocessing. *)
      let top (self : t) (c : lit A.t) (pr_c : proof_step) :
          lit A.t * proof_step =
        let steps = ref [] in

        (* simplify a literal, then preprocess it *)
        let[@inline] simp_lit lit =
          let lit, pr = simplify_and_preproc_lit_ self lit in
          Option.iter (fun pr -> steps := pr :: !steps) pr;
          lit
        in
        let c' = A.map simp_lit c in

        let pr_c' =
          if !steps = [] then
            pr_c
          else (
            Stat.incr self.count_preprocess_clause;
            P.lemma_rw_clause pr_c ~res:(A.to_iter c')
              ~using:(Iter.of_list !steps) self.proof
          )
        in
        c', pr_c'
    end
    [@@inline]

    module PC_list = Preprocess_clause (CCList)
    module PC_arr = Preprocess_clause (CCArray)

    let preprocess_clause_ = PC_list.top
    let preprocess_clause_iarray_ = PC_arr.top

    module type PERFORM_ACTS = sig
      type t

      val add_clause :
        solver -> t -> keep:bool -> lit list -> proof_step -> unit

      val add_lit : solver -> t -> ?default_pol:bool -> lit -> unit
    end

    module Perform_delayed (A : PERFORM_ACTS) = struct
      (* perform actions that were delayed *)
      let top (self : t) (acts : A.t) : unit =
        while not (Queue.is_empty self.delayed_actions) do
          let act = Queue.pop self.delayed_actions in
          match act with
          | DA_add_clause { c; pr = pr_c; keep } ->
            let c', pr_c' = preprocess_clause_ self c pr_c in
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

    let[@inline] add_clause_temp self _acts c (proof : proof_step) : unit =
      let c, proof = preprocess_clause_ self c proof in
      delayed_add_clause self ~keep:false c proof

    let[@inline] add_clause_permanent self _acts c (proof : proof_step) : unit =
      let c, proof = preprocess_clause_ self c proof in
      delayed_add_clause self ~keep:true c proof

    let[@inline] mk_lit (self : t) (_acts : theory_actions) ?sign t : lit =
      Lit.atom self.tst ?sign t

    let[@inline] add_lit self _acts ?default_pol lit =
      delayed_add_lit self ?default_pol lit

    let add_lit_t self _acts ?sign t =
      let lit = Lit.atom self.tst ?sign t in
      let lit, _ = simplify_and_preproc_lit_ self lit in
      delayed_add_lit self lit

    let on_final_check self f = self.on_final_check <- f :: self.on_final_check

    let on_partial_check self f =
      self.on_partial_check <- f :: self.on_partial_check

    let on_cc_new_term self f = CC.on_new_term (cc self) f
    let on_cc_pre_merge self f = CC.on_pre_merge (cc self) f
    let on_cc_post_merge self f = CC.on_post_merge (cc self) f
    let on_cc_conflict self f = CC.on_conflict (cc self) f
    let on_cc_propagate self f = CC.on_propagate (cc self) f
    let on_cc_is_subterm self f = CC.on_is_subterm (cc self) f
    let cc_add_term self t = CC.add_term (cc self) t
    let cc_mem_term self t = CC.mem_term (cc self) t
    let cc_find self n = CC.find (cc self) n

    let cc_are_equal self t1 t2 =
      let n1 = cc_add_term self t1 in
      let n2 = cc_add_term self t2 in
      N.equal (cc_find self n1) (cc_find self n2)

    let cc_merge self _acts n1 n2 e = CC.merge (cc self) n1 n2 e

    let cc_merge_t self acts t1 t2 e =
      cc_merge self acts (cc_add_term self t1) (cc_add_term self t2) e

    let cc_raise_conflict_expl self acts e =
      CC.raise_conflict_from_expl (cc self) acts e

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

    let push_level (self : t) : unit =
      self.level <- 1 + self.level;
      CC.push_level (cc self);
      push_lvl_ self.th_states

    let pop_levels (self : t) n : unit =
      self.last_model <- None;
      self.level <- self.level - n;
      CC.pop_levels (cc self) n;
      pop_lvls_ n self.th_states

    (** {2 Model construction and theory combination} *)

    (* make model from the congruence closure *)
    let mk_model_ (self : t) : Model.t =
      Log.debug 1 "(smt.solver.mk-model)";
      Profile.with_ "smt-solver.mk-model" @@ fun () ->
      let module M = Term.Tbl in
      let { cc = (lazy cc); model_ask = model_ask_hooks; model_complete; _ } =
        self
      in

      let model = M.create 128 in
      (* populate with information from the CC *)
      CC.get_model_for_each_class cc (fun (_, ts, v) ->
          Iter.iter
            (fun n ->
              let t = N.term n in
              M.replace model t v)
            ts);

      (* complete model with theory specific values *)
      let complete_with f =
        f self ~add:(fun t u ->
            if not (M.mem model t) then (
              Log.debugf 20 (fun k ->
                  k "(@[smt.model-complete@ %a@ :with-val %a@])" Term.pp t
                    Term.pp u);
              M.replace model t u
            ))
      in
      List.iter complete_with model_complete;

      (* compute a value for [n]. *)
      let rec val_for_class (n : N.t) : term =
        Log.debugf 5 (fun k -> k "val-for-term %a" N.pp n);
        let repr = CC.find cc n in
        Log.debugf 5 (fun k -> k "val-for-term.repr %a" N.pp repr);

        (* see if a value is found already (always the case if it's a boolean) *)
        match M.get model (N.term repr) with
        | Some t_val ->
          Log.debugf 5 (fun k -> k "cached val is %a" Term.pp t_val);
          t_val
        | None ->
          (* try each model hook *)
          let rec try_hooks_ = function
            | [] -> N.term repr
            | h :: hooks ->
              (match h ~recurse:(fun _ n -> val_for_class n) self repr with
              | None -> try_hooks_ hooks
              | Some t -> t)
          in

          let t_val =
            match
              (* look for a value in the model for any term in the class *)
              N.iter_class repr
              |> Iter.find_map (fun n -> M.get model (N.term n))
            with
            | Some v -> v
            | None -> try_hooks_ model_ask_hooks
          in

          M.replace model (N.term repr) t_val;
          (* be sure to cache the value *)
          Log.debugf 5 (fun k -> k "val is %a" Term.pp t_val);
          t_val
      in

      (* map terms of each CC class to the value computed for their class. *)
      CC.all_classes cc (fun repr ->
          let t_val = val_for_class repr in
          (* value for this class *)
          N.iter_class repr (fun u ->
              let t_u = N.term u in
              if (not (N.equal u repr)) && not (Term.equal t_u t_val) then
                M.replace model t_u t_val));
      Model.Map model

    (* do theory combination using the congruence closure. Each theory
       can merge classes, *)
    let check_th_combination_ (self : t) (acts : theory_actions) :
        (Model.t, th_combination_conflict) result =
      let cc = cc self in
      (* entier model mode, disabling most of congruence closure *)
      CC.with_model_mode cc @@ fun () ->
      let set_val (t, v) : unit =
        Log.debugf 50 (fun k ->
            k "(@[solver.th-comb.cc-set-term-value@ %a@ :val %a@])" Term.pp t
              Term.pp v);
        CC.set_model_value cc t v
      in

      (* obtain assignments from the hook, and communicate them to the CC *)
      let add_th_values f : unit =
        let vals = f self acts in
        Iter.iter set_val vals
      in

      try
        List.iter add_th_values self.on_th_combination;
        CC.check cc acts;
        let m = mk_model_ self in
        Ok m
      with Semantic_conflict c -> Error c

    (* handle a literal assumed by the SAT solver *)
    let assert_lits_ ~final (self : t) (acts : theory_actions)
        (lits : Lit.t Iter.t) : unit =
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
      CC.check cc acts;
      if final then (
        List.iter (fun f -> f self acts lits) self.on_final_check;
        CC.check cc acts;

        (match check_th_combination_ self acts with
        | Ok m -> self.last_model <- Some m
        | Error { lits; semantic } ->
          (* bad model, we add a clause to remove it *)
          Log.debugf 5 (fun k ->
              k
                "(@[solver.th-comb.conflict@ :lits (@[%a@])@ :same-val \
                 (@[%a@])@])"
                (Util.pp_list Lit.pp) lits
                (Util.pp_list @@ Fmt.Dump.(triple bool Term.pp Term.pp))
                semantic);

          let c1 = List.rev_map Lit.neg lits in
          let c2 =
            semantic
            |> List.rev_map (fun (sign, t, u) ->
                   let eqn = A.mk_eq self.tst t u in
                   let lit = Lit.atom ~sign:(not sign) self.tst eqn in
                   (* make sure to consider the new lit *)
                   add_lit self acts lit;
                   lit)
          in

          let c = List.rev_append c1 c2 in
          let pr = P.lemma_cc (Iter.of_list c) self.proof in

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
      self.on_progress ();
      assert_lits_ ~final self acts iter;
      Profile.exit pb

    (* propagation from the bool solver *)
    let[@inline] partial_check (self : t) (acts : _ Sidekick_sat.acts) : unit =
      check_ ~final:false self acts

    (* perform final check of the model *)
    let[@inline] final_check (self : t) (acts : _ Sidekick_sat.acts) : unit =
      check_ ~final:true self acts

    let declare_pb_is_incomplete self =
      if self.complete then Log.debug 1 "(solver.declare-pb-is-incomplete)";
      self.complete <- false

    let create ~stat ~proof (tst : Term.store) (ty_st : Ty.store) () : t =
      let rec self =
        {
          tst;
          ty_st;
          cc =
            lazy
              ((* lazily tie the knot *)
               CC.create ~size:`Big self.tst self.proof);
          proof;
          th_states = Ths_nil;
          stat;
          simp = Simplify.create tst ty_st ~proof;
          last_model = None;
          on_progress = (fun () -> ());
          preprocess = [];
          model_ask = [];
          model_complete = [];
          registry = Registry.create ();
          preprocessed = Term.Tbl.create 32;
          delayed_actions = Queue.create ();
          count_axiom = Stat.mk_int stat "solver.th-axioms";
          count_preprocess_clause = Stat.mk_int stat "solver.preprocess-clause";
          count_propagate = Stat.mk_int stat "solver.th-propagations";
          count_conflict = Stat.mk_int stat "solver.th-conflicts";
          on_partial_check = [];
          on_final_check = [];
          on_th_combination = [];
          level = 0;
          complete = true;
        }
      in
      ignore (Lazy.force @@ self.cc : CC.t);
      self
  end

  module Sat_solver = Sidekick_sat.Make_cdcl_t (Solver_internal)
  (** the parametrized SAT Solver *)

  module Registry = Solver_internal.Registry

  module type THEORY = sig
    type t

    val name : string
    val create_and_setup : Solver_internal.t -> t
    val push_level : t -> unit
    val pop_levels : t -> int -> unit
  end

  type theory = (module THEORY)
  type 'a theory_p = (module THEORY with type t = 'a)

  (** {2 Result} *)

  module Unknown = struct
    type t = U_timeout | U_max_depth | U_incomplete | U_asked_to_stop

    let pp out = function
      | U_timeout -> Fmt.string out {|"timeout"|}
      | U_max_depth -> Fmt.string out {|"max depth reached"|}
      | U_incomplete -> Fmt.string out {|"incomplete fragment"|}
      | U_asked_to_stop -> Fmt.string out {|"asked to stop by callback"|}
  end
  [@@ocaml.warning "-37"]

  type res =
    | Sat of Model.t
    | Unsat of {
        unsat_core: unit -> lit Iter.t;
            (** Unsat core (subset of assumptions), or empty *)
        unsat_proof_step: unit -> proof_step option;
            (** Proof step for the empty clause *)
      }
    | Unknown of Unknown.t
        (** Result of solving for the current set of clauses *)

  (* main solver state *)
  type t = {
    si: Solver_internal.t;
    solver: Sat_solver.t;
    mutable last_res: res option;
    stat: Stat.t;
    proof: P.t;
    count_clause: int Stat.counter;
    count_solve: int Stat.counter; (* config: Config.t *)
  }

  type solver = t

  (** {2 Main} *)

  let add_theory_p (type a) (self : t) (th : a theory_p) : a =
    let (module Th) = th in
    Log.debugf 2 (fun k -> k "(@[smt-solver.add-theory@ :name %S@])" Th.name);
    let st = Th.create_and_setup self.si in
    (* add push/pop to the internal solver *)
    (let open Solver_internal in
    self.si.th_states <-
      Ths_cons
        {
          st;
          push_level = Th.push_level;
          pop_levels = Th.pop_levels;
          next = self.si.th_states;
        });
    st

  let add_theory (self : t) (th : theory) : unit =
    let (module Th) = th in
    ignore (add_theory_p self (module Th))

  let add_theory_l self = List.iter (add_theory self)

  (* create a new solver *)
  let create ?(stat = Stat.global) ?size ~proof ~theories tst ty_st () : t =
    Log.debug 5 "smt-solver.create";
    let si = Solver_internal.create ~stat ~proof tst ty_st () in
    let self =
      {
        si;
        proof;
        last_res = None;
        solver = Sat_solver.create ~proof ?size ~stat si;
        stat;
        count_clause = Stat.mk_int stat "solver.add-clause";
        count_solve = Stat.mk_int stat "solver.solve";
      }
    in
    add_theory_l self theories;
    (* assert [true] and [not false] *)
    (let tst = Solver_internal.tst self.si in
     let t_true = Term.bool tst true in
     Sat_solver.add_clause self.solver
       [ Lit.atom tst t_true ]
       (P.lemma_true t_true self.proof));
    self

  let[@inline] solver self = self.solver
  let[@inline] cc self = Solver_internal.cc self.si
  let[@inline] stats self = self.stat
  let[@inline] tst self = Solver_internal.tst self.si
  let[@inline] ty_st self = Solver_internal.ty_st self.si
  let[@inline] proof self = self.si.proof
  let[@inline] last_res self = self.last_res
  let[@inline] registry self = Solver_internal.registry self.si
  let reset_last_res_ self = self.last_res <- None

  (* preprocess clause, return new proof *)
  let preprocess_clause_ (self : t) (c : lit array) (pr : proof_step) :
      lit array * proof_step =
    Solver_internal.preprocess_clause_iarray_ self.si c pr

  let mk_lit_t (self : t) ?sign (t : term) : lit =
    let lit = Lit.atom self.si.tst ?sign t in
    let lit, _ = Solver_internal.simplify_and_preproc_lit_ self.si lit in
    lit

  (** {2 Main} *)

  let pp_stats out (self : t) : unit = Stat.pp_all out (Stat.all @@ stats self)

  (* add [c], without preprocessing its literals *)
  let add_clause_nopreproc_ (self : t) (c : lit array) (proof : proof_step) :
      unit =
    Stat.incr self.count_clause;
    reset_last_res_ self;
    Log.debugf 50 (fun k ->
        k "(@[solver.add-clause@ %a@])" (Util.pp_array Lit.pp) c);
    let pb = Profile.begin_ "add-clause" in
    Sat_solver.add_clause_a self.solver (c :> lit array) proof;
    Profile.exit pb

  let add_clause_nopreproc_l_ self c p =
    add_clause_nopreproc_ self (CCArray.of_list c) p

  module Perform_delayed_ = Solver_internal.Perform_delayed (struct
    type nonrec t = t

    let add_clause _si solver ~keep:_ c pr : unit =
      add_clause_nopreproc_l_ solver c pr

    let add_lit _si solver ?default_pol lit : unit =
      Sat_solver.add_lit solver.solver ?default_pol lit
  end)

  let add_clause (self : t) (c : lit array) (proof : proof_step) : unit =
    let c, proof = preprocess_clause_ self c proof in
    add_clause_nopreproc_ self c proof;
    Perform_delayed_.top self.si self;
    (* finish preproc *)
    ()

  let add_clause_l self c p = add_clause self (CCArray.of_list c) p

  let assert_terms self c =
    let c = CCList.map (fun t -> Lit.atom (tst self) t) c in
    let pr_c = P.emit_input_clause (Iter.of_list c) self.proof in
    add_clause_l self c pr_c

  let assert_term self t = assert_terms self [ t ]

  exception Resource_exhausted = Sidekick_sat.Resource_exhausted

  let solve ?(on_exit = []) ?(check = true) ?(on_progress = fun _ -> ())
      ?(should_stop = fun _ _ -> false) ~assumptions (self : t) : res =
    Profile.with_ "smt-solver.solve" @@ fun () ->
    let do_on_exit () = List.iter (fun f -> f ()) on_exit in

    let on_progress =
      let resource_counter = ref 0 in
      fun () ->
        incr resource_counter;
        on_progress self;
        if should_stop self !resource_counter then
          raise_notrace Resource_exhausted
    in
    self.si.on_progress <- on_progress;

    let res =
      match
        Stat.incr self.count_solve;
        Sat_solver.solve ~on_progress ~assumptions (solver self)
      with
      | Sat_solver.Sat _ when not self.si.complete ->
        Log.debugf 1 (fun k ->
            k
              "(@[sidekick.smt-solver: SAT@ actual: UNKNOWN@ :reason \
               incomplete-fragment@])");
        Unknown Unknown.U_incomplete
      | Sat_solver.Sat _ ->
        Log.debug 1 "(sidekick.smt-solver: SAT)";

        Log.debugf 5 (fun k ->
            let ppc out n =
              Fmt.fprintf out "{@[<hv>class@ %a@]}" (Util.pp_iter N.pp)
                (N.iter_class n)
            in
            k "(@[sidekick.smt-solver.classes@ (@[%a@])@])" (Util.pp_iter ppc)
              (CC.all_classes @@ Solver_internal.cc self.si));

        let m =
          match self.si.last_model with
          | Some m -> m
          | None -> assert false
        in
        (* TODO: check model *)
        let _ = check in

        do_on_exit ();
        Sat m
      | Sat_solver.Unsat (module UNSAT) ->
        let unsat_core () = UNSAT.unsat_assumptions () in
        let unsat_proof_step () = Some (UNSAT.unsat_proof ()) in
        do_on_exit ();
        Unsat { unsat_core; unsat_proof_step }
      | exception Resource_exhausted -> Unknown Unknown.U_asked_to_stop
    in
    self.last_res <- Some res;
    res

  let push_assumption self a =
    reset_last_res_ self;
    Sat_solver.push_assumption self.solver a

  let pop_assumptions self n =
    reset_last_res_ self;
    Sat_solver.pop_assumptions self.solver n

  type propagation_result =
    | PR_sat
    | PR_conflict of { backtracked: int }
    | PR_unsat of { unsat_core: unit -> lit Iter.t }

  let check_sat_propagations_only ~assumptions self : propagation_result =
    reset_last_res_ self;
    match Sat_solver.check_sat_propagations_only ~assumptions self.solver with
    | Sat_solver.PR_sat -> PR_sat
    | Sat_solver.PR_conflict { backtracked } -> PR_conflict { backtracked }
    | Sat_solver.PR_unsat (module UNSAT) ->
      let unsat_core () = UNSAT.unsat_assumptions () in
      PR_unsat { unsat_core }

  let mk_theory (type st) ~name ~create_and_setup ?(push_level = fun _ -> ())
      ?(pop_levels = fun _ _ -> ()) () : theory =
    let module Th = struct
      type t = st

      let name = name
      let create_and_setup = create_and_setup
      let push_level = push_level
      let pop_levels = pop_levels
    end in
    (module Th : THEORY)
end
