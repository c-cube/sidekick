open Sigs

open struct
  module SI = Solver_internal
  module P = Proof_trace
  module Rule_ = Proof_core
end

(* TODO
   let mk_cc_acts_ (pr : P.t) (a : sat_acts) : CC.actions =
     let (module A) = a in

     (module struct
       module T = T
       module Lit = Lit

       type nonrec lit = lit
       type nonrec term = term
       type nonrec proof_trace = Proof_trace.t
       type nonrec step_id = step_id

       let proof_trace () = pr
       let[@inline] raise_conflict lits (pr : step_id) = A.raise_conflict lits pr

       let[@inline] raise_semantic_conflict lits semantic =
         raise (Semantic_conflict { lits; semantic })

       let[@inline] propagate lit ~reason =
         let reason = Sidekick_sat.Consequence reason in
         A.propagate lit reason
     end)
*)

module Sat_solver = Sidekick_sat
(** the parametrized SAT Solver *)

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
      unsat_step_id: unit -> step_id option;
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
  n_clause_input: int Stat.counter;
  n_clause_internal: int Stat.counter;
  n_solve: int Stat.counter; (* config: Config.t *)
}

(** {2 Main} *)

type theory = Theory.t

let mk_theory = Theory.make

let add_theory_p (type a) (self : t) (th : a Theory.p) : a =
  let (module Th) = th in
  Log.debugf 2 (fun k -> k "(@[smt-solver.add-theory@ :name %S@])" Th.name);
  let st = Th.create_and_setup self.si in
  (* add push/pop to the internal solver *)
  Solver_internal.add_theory_state self.si ~st ~push_level:Th.push_level
    ~pop_levels:Th.pop_levels;
  st

let add_theory (self : t) (th : theory) : unit =
  let (module Th) = th in
  ignore (add_theory_p self (module Th))

let add_theory_l self = List.iter (add_theory self)

(* create a new solver *)
let create arg ?(stat = Stat.global) ?size ~proof ~theories tst () : t =
  Log.debug 5 "smt-solver.create";
  let si = Solver_internal.create arg ~stat ~proof tst () in
  let self =
    {
      si;
      proof;
      last_res = None;
      solver = Sat_solver.create ~proof ?size ~stat (SI.to_sat_plugin si);
      stat;
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
     [ Lit.atom t_true ]
     (P.add_step self.proof @@ fun () -> Rule_.lemma_true t_true));
  self

let[@inline] solver self = self.solver
let[@inline] stats self = self.stat
let[@inline] tst self = Solver_internal.tst self.si
let[@inline] proof self = self.proof
let[@inline] last_res self = self.last_res
let[@inline] registry self = Solver_internal.registry self.si
let reset_last_res_ self = self.last_res <- None

(* preprocess clause, return new proof *)
let preprocess_clause_ (self : t) (c : lit array) (pr : step_id) :
    lit array * step_id =
  Solver_internal.preprocess_clause_array self.si c pr

let mk_lit_t (self : t) ?sign (t : term) : lit =
  let lit = Lit.atom ?sign t in
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
  Sat_solver.add_clause_a self.solver (c :> lit array) proof;
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

let add_clause (self : t) (c : lit array) (proof : step_id) : unit =
  let c, proof = preprocess_clause_ self c proof in
  add_clause_nopreproc_ ~internal:false self c proof;
  Perform_delayed_.top self.si self;
  (* finish preproc *)
  ()

let add_clause_l self c p = add_clause self (CCArray.of_list c) p

let assert_terms self c =
  let c = CCList.map Lit.atom c in
  let pr_c = P.add_step self.proof @@ fun () -> Proof_sat.sat_input_clause c in
  add_clause_l self c pr_c

let assert_term self t = assert_terms self [ t ]

let solve ?(on_exit = []) ?(check = true) ?(on_progress = fun _ -> ())
    ?(should_stop = fun _ _ -> false) ~assumptions (self : t) : res =
  let@ () = Profile.with_ "smt-solver.solve" in
  let do_on_exit () = List.iter (fun f -> f ()) on_exit in

  let on_progress =
    let resource_counter = ref 0 in
    fun () ->
      incr resource_counter;
      on_progress self;
      if should_stop self !resource_counter then
        raise_notrace Resource_exhausted
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
    | Sat_solver.Sat _ ->
      Log.debug 1 "(sidekick.smt-solver: SAT)";

      Log.debugf 5 (fun k ->
          let ppc out n =
            Fmt.fprintf out "{@[<hv>class@ %a@]}" (Util.pp_iter E_node.pp)
              (E_node.iter_class n)
          in
          k "(@[sidekick.smt-solver.classes@ (@[%a@])@])" (Util.pp_iter ppc)
            (CC.all_classes @@ Solver_internal.cc self.si));

      let m =
        match SI.last_model self.si with
        | Some m -> m
        | None -> assert false
      in
      (* TODO: check model *)
      let _ = check in

      do_on_exit ();
      Sat m
    | Sat_solver.Unsat (module UNSAT) ->
      let unsat_core () = UNSAT.unsat_assumptions () in
      let unsat_step_id () = Some (UNSAT.unsat_proof ()) in
      do_on_exit ();
      Unsat { unsat_core; unsat_step_id }
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
