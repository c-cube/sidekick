open Sigs

open struct
  module SI = Solver_internal
end

module Check_res = Sidekick_abstract_solver.Check_res

module Sat_solver = Sidekick_sat
(** the parametrized SAT Solver *)

module Unknown = Sidekick_abstract_solver.Unknown [@@ocaml.warning "-37"]

type value = Term.t

type sat_result = Check_res.sat_result = {
  get_value: Term.t -> value option;  (** Value for this term *)
  iter_classes: (Term.t Iter.t * value) Iter.t;
      (** All equivalence classes in the congruence closure *)
  eval_lit: Lit.t -> bool option;  (** Evaluate literal *)
  iter_true_lits: Lit.t Iter.t;
      (** Iterate on literals that are true in the trail *)
}
(** Satisfiable *)

type unsat_result = Check_res.unsat_result = {
  unsat_core: unit -> Lit.t Iter.t;
      (** Unsat core (subset of assumptions), or empty *)
  unsat_proof: unit -> Sidekick_proof.Step.id option;
      (** Proof step for the empty clause *)
}
(** Unsatisfiable *)

(** Result of solving for the current set of clauses *)
type res = Check_res.t =
  | Sat of sat_result
  | Unsat of unsat_result
  | Unknown of Unknown.t
      (** Unknown, obtained after a timeout, memory limit, etc. *)

(* main solver state *)
type t = {
  si: Solver_internal.t;
  solver: Sat_solver.t;
  mutable last_res: res option;
  stat: Stat.t;
  tracer: Tracer.t; [@ocaml.warn "-69"]
  theory_id_gen: Theory_id.state;
  n_clause_input: int Stat.counter;
  n_clause_internal: int Stat.counter;
  n_solve: int Stat.counter; (* config: Config.t *)
}

(** {2 Main} *)

type theory = Theory.t

let mk_theory = Theory.make

let add_theory_p (type a) (self : t) (th : a Theory.p) : a =
  let (module Th) = th in
  let th_id = Theory_id.fresh self.theory_id_gen in
  Log.debugf 2 (fun k ->
      k "(@[smt-solver.add-theory@ :id %a@ :name %S@])" Theory_id.pp th_id
        Th.name);
  let st = Th.create_and_setup ~id:th_id self.si in
  (* add push/pop to the internal solver *)
  Solver_internal.add_theory_state self.si ~st ~push_level:Th.push_level
    ~pop_levels:Th.pop_levels;
  st

let add_theory (self : t) (th : theory) : unit =
  let (module Th) = th in
  ignore (add_theory_p self (module Th))

let add_theory_l self = List.iter (add_theory self)

(* create a new solver *)
let create arg ?(stat = Stat.global) ?size ~tracer ~theories tst () : t =
  Log.debug 5 "smt-solver.create";
  let si = Solver_internal.create arg ~stat ~tracer tst () in
  let self =
    {
      si;
      tracer;
      last_res = None;
      solver = Sat_solver.create ?size ~tracer ~stat (SI.to_sat_plugin si);
      stat;
      theory_id_gen = Theory_id.create ();
      n_clause_input = Stat.mk_int stat "smt.solver.add-clause.input";
      n_clause_internal = Stat.mk_int stat "smt.solver.add-clause.internal";
      n_solve = Stat.mk_int stat "smt.solver.solve";
    }
  in
  add_theory_l self theories;
  (* assert [true] and [not false] *)
  (let tst = Solver_internal.tst self.si in
   let t_true = Term.true_ tst in
   Sat_solver.add_clause self.solver
     [ Lit.atom tst t_true ]
     (fun () -> Proof.Core_rules.lemma_true t_true));
  self

let default_arg =
  (module struct
    let view_as_cc = Default_cc_view.view_as_cc
  end : ARG)

let create_default ?stat ?size ~tracer ~theories tst () : t =
  create default_arg ?stat ?size ~tracer ~theories tst ()

let[@inline] solver self = self.solver
let[@inline] stats self = self.stat
let[@inline] tst self = Solver_internal.tst self.si
let[@inline] tracer self = self.tracer
let[@inline] last_res self = self.last_res
let[@inline] registry self = Solver_internal.registry self.si
let reset_last_res_ self = self.last_res <- None

(* preprocess clause, return new proof *)
let preprocess_clause_ (self : t) (c : lit array) (pr : step_id) :
    lit array * step_id =
  Solver_internal.preprocess_clause_array self.si c pr

let mk_lit_t (self : t) ?sign (t : term) : lit =
  let lit = Lit.atom ?sign (tst self) t in
  let lit, _ = Solver_internal.simplify_and_preproc_lit self.si lit in
  lit

(** {2 Main} *)

let pp_stats out (self : t) : unit = Stat.pp out (stats self)

(* add [c], without preprocessing its literals *)
let add_clause_nopreproc_ ~internal (self : t) (c : lit array) (proof : step_id)
    : unit =
  if internal then
    Stat.incr self.n_clause_internal
  else
    Stat.incr self.n_clause_input;
  reset_last_res_ self;
  Log.debugf 50 (fun k ->
      k "(@[solver.add-clause@ %a@])" (Util.pp_array Lit.pp) c);
  let pb = Profile.begin_ "add-clause" in
  Sat_solver.add_clause_a self.solver
    (c :> lit array)
    (fun () -> Proof.Pterm.ref proof);
  Profile.exit pb

let add_clause_nopreproc_l_ ~internal self c p =
  add_clause_nopreproc_ ~internal self (CCArray.of_list c) p

module Perform_delayed_ = Solver_internal.Perform_delayed (struct
  type nonrec t = t

  let add_clause _si solver ~keep:_ c pr : unit =
    add_clause_nopreproc_l_ ~internal:true solver c pr

  let add_lit _si solver ?default_pol lit : unit =
    Sat_solver.add_lit solver.solver ?default_pol lit
end)

let add_clause (self : t) (c : lit array) (proof : Proof.Pterm.delayed) : unit =
  let proof = Proof.Tracer.add_step self.tracer proof in
  let c, proof = preprocess_clause_ self c proof in
  Tracer.assert_clause' self.tracer ~id:0 (Iter.of_array c) proof;
  add_clause_nopreproc_ ~internal:false self c proof;
  Perform_delayed_.top self.si self;
  (* finish preproc *)
  ()

let add_clause_l self c p = add_clause self (CCArray.of_list c) p

let assert_terms self c =
  let c = CCList.map (Lit.atom (tst self)) c in
  let pr_c () = Proof.Sat_rules.sat_input_clause c in
  add_clause_l self c pr_c

let assert_term self t = assert_terms self [ t ]
let add_ty (self : t) ty = SI.add_ty self.si ~ty

let solve ?(on_exit = []) ?(on_progress = fun _ -> ())
    ?(should_stop = fun _ -> false) ~assumptions (self : t) : res =
  let@ () = Profile.with_ "smt-solver.solve" in
  let do_on_exit () = List.iter (fun f -> f ()) on_exit in

  let on_progress =
    let resource_counter = ref 0 in
    fun () ->
      incr resource_counter;
      on_progress ();
      if should_stop !resource_counter then raise_notrace Resource_exhausted
  in
  Event.on ~f:on_progress (SI.on_progress self.si);

  let res =
    match
      Stat.incr self.n_solve;
      Sat_solver.solve ~on_progress ~assumptions (solver self)
    with
    | Sat_solver.Sat _ when not (SI.is_complete self.si) ->
      Log.debugf 1 (fun k ->
          k
            "(@[sidekick.smt-solver: SAT@ actual: UNKNOWN@ :reason \
             incomplete-fragment@])");
      Unknown Unknown.U_incomplete
    | Sat_solver.Sat (module SAT) ->
      Log.debug 1 "(sidekick.smt-solver: SAT)";

      let m =
        match SI.last_model self.si with
        | Some m -> m
        | None -> assert false
      in

      let iter_classes =
        CC.all_classes (Solver_internal.cc self.si)
        |> Iter.filter (fun repr ->
               not @@ Term.is_pi (Term.ty @@ E_node.term repr))
        |> Iter.map (fun repr ->
               let v =
                 match
                   (* find value for this class *)
                   Iter.find_map
                     (fun en -> Term.Map.get (E_node.term en) m)
                     (E_node.iter_class repr)
                 with
                 | None ->
                   Error.errorf
                     "(@[solver.mk-model.no-value-for-repr@ %a@ :ty %a@])"
                     E_node.pp repr Term.pp
                     (Term.ty @@ E_node.term repr)
                 | Some v -> v
               in
               let terms = E_node.iter_class repr |> Iter.map E_node.term in
               terms, v)
      in

      Log.debugf 5 (fun k ->
          let ppc out (cls, v) =
            Fmt.fprintf out "{@[<hv1>class@ :value %a@ %a@]}" Term.pp v
              (Util.pp_iter ~sep:";" Term.pp)
              cls
          in
          k "(@[sidekick.smt-solver.classes@ (@[%a@])@])" (Util.pp_iter ppc)
            iter_classes);

      do_on_exit ();
      Sat
        {
          get_value = (fun t -> Term.Map.get t m);
          iter_classes;
          eval_lit =
            (fun l ->
              try Some (SAT.eval l) with Sat_solver.UndecidedLit -> None);
          iter_true_lits = SAT.iter_trail;
        }
    | Sat_solver.Unsat (module UNSAT) ->
      let unsat_core () = UNSAT.unsat_assumptions () in
      let unsat_proof () = Some (UNSAT.unsat_proof ()) in
      do_on_exit ();
      Unsat { unsat_core; unsat_proof }
    | exception Resource_exhausted -> Unknown Unknown.U_asked_to_stop
  in
  self.last_res <- Some res;
  res

let as_asolver (self : t) : Sidekick_abstract_solver.Asolver.t =
  object
    method assert_term t : unit = assert_term self t
    method assert_clause c p : unit = add_clause self c p
    method assert_clause_l c p : unit = add_clause_l self c p
    method lit_of_term ?sign t : Lit.t = mk_lit_t self ?sign t
    method proof_tracer = (self.tracer :> Proof.Tracer.t)
    method last_res = last_res self
    method add_ty ~ty = add_ty self ty

    method solve ?on_exit ?on_progress ?should_stop ~assumptions () : res =
      solve ?on_exit ?on_progress ?should_stop ~assumptions self
  end

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
