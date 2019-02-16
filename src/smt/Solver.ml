
(* This file is free software. See file "license" for more details. *)

(** {1 Main Solver} *)

[@@@warning "-32"]

open Solver_types

let get_time : unit -> float = Sys.time

(** {2 The Main Solver} *)

module Sat_solver = Msat.Make_cdcl_t(Theory_combine)

let[@inline] clause_of_mclause (c:Sat_solver.clause): Lit.t IArray.t =
  Sat_solver.Clause.atoms c |> Array.map Sat_solver.Atom.formula |> IArray.of_array_unsafe

module Atom = Sat_solver.Atom
module Proof = Sat_solver.Proof

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

let[@inline] mk_atom_lit self lit : Atom.t = Sat_solver.make_atom self.solver lit
let[@inline] mk_atom_t self ?sign t : Atom.t =
  let lit = Lit.atom (tst self)  ?sign t in
  mk_atom_lit self lit

let create ?size ?(config=Config.empty) ?store_proof ~theories () : t =
  let th_combine = Theory_combine.create() in
  let self = {
    solver=Sat_solver.create ?store_proof ?size th_combine;
    stat=Stat.create ();
    config;
  } in
  (* now add the theories *)
  Theory_combine.add_theory_l th_combine theories;
  (* assert [true] and [not false] *)
  let tst = tst self in
  Sat_solver.assume self.solver [
    [Lit.atom tst @@ Term.true_ tst];
  ] Proof_default;
  self

(** {2 Sat Solver} *)

let print_progress (st:t) : unit =
  Printf.printf "\r[%.2f] clauses %d | lemmas %d%!"
    (get_time())
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
  | Unsat of Proof.t option
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
     :num_clause_push %d@ \
     :num_clause_tautology %d@ \
     :num_propagations %d@ \
     @])"
    s.stat.Stat.num_clause_push
    s.stat.Stat.num_clause_tautology
    s.stat.Stat.num_propagations

let do_on_exit ~on_exit =
  List.iter (fun f->f()) on_exit;
  ()

let assume (self:t) (c:Lit.t IArray.t) : unit =
  let sat = solver self in
  let c = IArray.to_array_map (Sat_solver.make_atom sat) c in
  Sat_solver.add_clause_a sat c Proof_default

(* TODO: remove? use a special constant + micro theory instead? *)
let[@inline] assume_distinct self l ~neq lit : unit =
  CC.assert_distinct (cc self) l lit ~neq

let check_model (_s:t) : unit =
  Log.debug 1 "(smt.solver.check-model)";
  (* TODO
  Sat_solver.check_model s.solver
  *)
  ()

(* TODO: main loop with iterative deepening of the unrolling  limit
   (not the value depth limit) *)
let solve ?(on_exit=[]) ?(check=true) ~assumptions (self:t) : res =
  let r = Sat_solver.solve ~assumptions (solver self) in
  match r with
  | Sat_solver.Sat st ->
    Log.debugf 1 (fun k->k "SAT");
    let lits f = st.iter_trail f (fun _ -> ()) in
    let m = Theory_combine.mk_model (th_combine self) lits in
    do_on_exit ~on_exit;
    Sat m
    (*
    let env = Ast.env_empty in
    let m = Model.make ~env in
       …
    Unknown U_incomplete (* TODO *)
    *)
  | Sat_solver.Unsat us ->
    let pr =
      try
        let pr = us.get_proof () in
        if check then Sat_solver.Proof.check pr;
        Some pr
      with Msat.Solver_intf.No_proof -> None
    in
    do_on_exit ~on_exit;
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
