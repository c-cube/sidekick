
(* This file is free software. See file "license" for more details. *)

(** {1 Main Solver} *)

open Solver_types

let get_time : unit -> float = Sys.time

(** {2 The Main Solver} *)

type level = int

module Sat_solver = Sidekick_sat.Make(Theory_combine)

let[@inline] clause_of_mclause (c:Sat_solver.clause): Lit.t IArray.t =
  Sat_solver.Clause.forms c

module Proof = struct
  type t = Sat_solver.Proof.t

  let check = Sat_solver.Proof.check

  let pp out (p:t) : unit =
    let pp_step_res out p =
      let {Sat_solver.Proof.conclusion; _ } = Sat_solver.Proof.expand p in
      Sat_solver.Clause.pp out conclusion
    in
    let pp_step out = function
      | Sat_solver.Proof.Lemma _ -> Format.fprintf out "(@[<1>lemma@ ()@])"
      | Sat_solver.Proof.Resolution (p1, p2, _) ->
        Format.fprintf out "(@[<1>resolution@ %a@ %a@])"
          pp_step_res p1 pp_step_res p2
      | _ -> Fmt.string out "<other>"
    in
    Format.fprintf out "(@[<v>";
    Sat_solver.Proof.fold
      (fun () {Sat_solver.Proof.conclusion; step } ->
         Format.fprintf out "(@[<hv1>step@ %a@ @[<1>from:@ %a@]@])@,"
           Sat_solver.Clause.pp conclusion pp_step step)
      () p;
    Format.fprintf out "@])";
    ()

end

(* main solver state *)
type t = {
  solver: Sat_solver.t;
  stat: Stat.t;
  config: Config.t
}

let[@inline] solver self = self.solver
let[@inline] th_combine (self:t) : Theory_combine.t = Sat_solver.theory self.solver
let[@inline] add_theory self th = Theory_combine.add_theory (th_combine self) th
let[@inline] cc self = Theory_combine.cc (th_combine self)
let stats self = self.stat
let[@inline] tst self = Theory_combine.tst (th_combine self)

let create ?size ?(config=Config.empty) ~theories () : t =
  let self = {
    solver=Sat_solver.create ?size ();
    stat=Stat.create ();
    config;
  } in
  (* now add the theories *)
  Theory_combine.add_theory_l (th_combine self) theories;
  self

(** {2 Sat Solver} *)

let print_progress (st:t) : unit =
  Printf.printf "\r[%.2f] expanded %d | clauses %d | lemmas %d%!"
    (get_time())
    st.stat.Stat.num_cst_expanded
    st.stat.Stat.num_clause_push
    st.stat.Stat.num_clause_tautology

let flush_progress (): unit =
  Printf.printf "\r%-80d\r%!" 0

(** {2 Toplevel Goals}

    List of toplevel goals to satisfy. Mainly used for checking purpose
*)

module Top_goals: sig
  val push : term -> unit
  val to_seq : term Sequence.t
  val check: unit -> unit
end = struct
  (* list of terms to fully evaluate *)
  let toplevel_goals_ : term list ref = ref []

  (* add [t] to the set of terms that must be evaluated *)
  let push (t:term): unit =
    toplevel_goals_ := t :: !toplevel_goals_;
    ()

  let to_seq k = List.iter k !toplevel_goals_

  (* FIXME
  (* check that this term fully evaluates to [true] *)
  let is_true_ (t:term): bool = match CC.normal_form t with
    | None -> false
    | Some (NF_bool b) -> b
    | Some (NF_cstor _) -> assert false (* not a bool *)

  let check () =
    if not (List.for_all is_true_ !toplevel_goals_)
    then (
      if Config.progress then flush_progress();
      Log.debugf 1
        (fun k->
           let pp_lit out t =
             let nf = CC.normal_form t in
             Format.fprintf out "(@[term: %a@ nf: %a@])"
               Term.pp t (Fmt.opt pp_term_nf) nf
           in
           k "(@[<hv1>Top_goals.check@ (@[<v>%a@])@])"
             (Util.pp_list pp_lit) !toplevel_goals_);
      assert false;
    )
  *)

  let check () : unit = ()
end

(** {2 Conversion} *)

(* list of constants we are interested in *)
let model_support_ : Cst.t list ref = ref []

let model_env_ : Ast.env ref = ref Ast.env_empty

let add_cst_support_ (c:cst): unit =
  CCList.Ref.push model_support_ c

let add_ty_support_ (_ty:Ty.t): unit = ()

(** {2 Result} *)

type unknown =
  | U_timeout
  | U_max_depth
  | U_incomplete

let pp_unknown out = function
  | U_timeout -> Fmt.string out "timeout"
  | U_max_depth -> Fmt.string out "max depth reached"
  | U_incomplete -> Fmt.string out "incomplete fragment"

type model = Model.t
let pp_model = Model.pp

type res =
  | Sat of model
  | Unsat of Proof.t
  | Unknown of unknown

(** {2 Main} *)

(* convert unsat-core *)
let clauses_of_unsat_core (core:Sat_solver.clause list): Lit.t IArray.t Sequence.t =
  Sequence.of_list core
  |> Sequence.map clause_of_mclause

(* print all terms reachable from watched literals *)
let pp_term_graph _out (_:t) =
  ()

let pp_stats out (s:t) : unit =
  Format.fprintf out
    "(@[<hv1>stats@ \
     :num_expanded %d@ \
     :num_uty_expanded %d@ \
     :num_clause_push %d@ \
     :num_clause_tautology %d@ \
     :num_propagations %d@ \
     :num_unif %d@ \
     @])"
    s.stat.Stat.num_cst_expanded
    s.stat.Stat.num_uty_expanded
    s.stat.Stat.num_clause_push
    s.stat.Stat.num_clause_tautology
    s.stat.Stat.num_propagations
    s.stat.Stat.num_unif

let do_on_exit ~on_exit =
  List.iter (fun f->f()) on_exit;
  ()

let assume (self:t) (c:Lit.t IArray.t) : unit =
  let sat = solver self in
  let c = Sat_solver.Clause.make (IArray.to_array_map (Sat_solver.Atom.make sat) c) in
  Sat_solver.add_clause ~permanent:true sat c

let[@inline] assume_eq self t u expl : unit =
  Congruence_closure.assert_eq (cc self) t u [expl]

let[@inline] assume_distinct self l ~neq lit : unit =
  Congruence_closure.assert_distinct (cc self) l lit ~neq

let check_model (s:t) = Sat_solver.check_model s.solver

(* TODO: main loop with iterative deepening of the unrolling  limit
   (not the value depth limit) *)
let solve ?on_exit:(_=[]) ?check:(_=true) ~assumptions (self:t) : res =
  let r = Sat_solver.solve ~assumptions (solver self) () in
  match r with
  | Sat_solver.Sat (Sidekick_sat.Sat_state st) ->
    Log.debugf 0 (fun k->k "SAT");
    let m = Theory_combine.mk_model (th_combine self) st.iter_trail in
    Sat m
    (*
    let env = Ast.env_empty in
    let m = Model.make ~env in
       …
    Unknown U_incomplete (* TODO *)
    *)
  | Sat_solver.Unsat (Sidekick_sat.Unsat_state us) ->
    let pr = us.get_proof () in
    Unsat pr

(* FIXME:
(* TODO: max_depth should actually correspond to the maximum depth
   of un-expanded terms (expand in body of t --> depth = depth(t)+1),
   so it corresponds to unfolding call graph to some depth *)

let solve ?(on_exit=[]) ?(check=true) () =
  let n_iter = ref 0 in
  let rec check_cc (): res =
    assert (Backtrack.at_level_0 ());
    if !n_iter > Config.max_depth then Unknown U_max_depth (* exceeded limit *)
    else begin match CC.check () with
      | CC.Unsat _ -> Unsat (* TODO proof *)
      | CC.Sat lemmas  ->
        add_cc_lemmas lemmas;
        check_solver()
    end

  and check_solver (): res =
    (* assume all literals [expanded t] are false *)
    let assumptions =
      Terms_to_expand.to_seq
      |> Sequence.map (fun {Terms_to_expand.lit; _} -> Lit.neg lit)
      |> Sequence.to_rev_list
    in
    incr n_iter;
    Log.debugf 2
      (fun k->k
          "(@[<1>@{<Yellow>solve@}@ @[:with-assumptions@ (@[%a@])@ n_iter: %d]@])"
          (Util.pp_list Lit.pp) assumptions !n_iter);
    begin match M.solve ~assumptions() with
      | M.Sat _ ->
        Log.debugf 1 (fun k->k "@{<Yellow>** found SAT@}");
        do_on_exit ~on_exit;
        let m = Model_build.make () in
        if check then Model_build.check m;
        Sat m
      | M.Unsat us ->
        let p = us.SI.get_proof () in
        Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
        let core = p |> M.unsat_core in
        (* check if unsat because of assumptions *)
        expand_next core
    end

  (* pick a term to expand, or UNSAT *)
  and expand_next (core:unsat_core) =
    begin match find_to_expand core with
      | None -> Unsat (* TODO proof *)
      | Some to_expand ->
        let t = to_expand.Terms_to_expand.term in
        Log.debugf 2 (fun k->k "(@[<1>@{<green>expand_next@}@ :term %a@])" Term.pp t);
        CC.expand_term t;
        Terms_to_expand.remove t;
        Clause.push_new (Clause.make [to_expand.Terms_to_expand.lit]);
        Backtrack.backtrack_to_level_0 ();
        check_cc () (* recurse *)
    end
  in
  check_cc()

   *)
