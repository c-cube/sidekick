
(* This file is free software. See file "license" for more details. *)

(** {1 Main Solver} *)

open Solver_types

let get_time : unit -> float = Sys.time

(** {2 The Main Solver} *)

type level = int

module Sat_solver = Dagon_sat.Make(Theory_combine)

let[@inline] clause_of_mclause (c:Sat_solver.clause): Lit.t IArray.t =
  Sat_solver.Clause.atoms c

module Proof = struct
  type t = Sat_solver.Proof.proof

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

(* FIXME: repair this and output a nice model.
module Model_build : sig
  val make: unit -> model

  val check : model -> unit
end = struct
  module ValueListMap = CCMap.Make(struct
      type t = Term.t list (* normal forms *)
      let compare = CCList.compare Term.compare
    end)

  type doms = {
    dom_of_ty: ID.t list Ty.Tbl.t; (* uninterpreted type -> domain elements *)
    dom_of_class: term Term.Tbl.t; (* representative -> normal form *)
    dom_of_cst: term Cst.Tbl.t; (* cst -> its normal form *)
    dom_of_fun: term ValueListMap.t Cst.Tbl.t; (* function -> args -> normal form *)
    dom_traversed: unit Term.Tbl.t; (* avoid cycles *)
  }

  let create_doms() : doms =
    { dom_of_ty=Ty.Tbl.create 32;
      dom_of_class = Term.Tbl.create 32;
      dom_of_cst=Cst.Tbl.create 32;
      dom_of_fun=Cst.Tbl.create 32;
      dom_traversed=Term.Tbl.create 128;
    }

  (* pick a term belonging to this type.
     we just generate a new constant, as picking true/a constructor might
     refine the partial model into an unsatisfiable state. *)
  let pick_default ~prefix (doms:doms)(ty:Ty.t) : term =
    (* introduce a fresh constant for this equivalence class *)
    let elts = Ty.Tbl.get_or ~default:[] doms.dom_of_ty ty in
    let cst = ID.makef "%s%s_%d" prefix (Ty.mangle ty) (List.length elts) in
    let nf = Term.const (Cst.make_undef cst ty) in
    Ty.Tbl.replace doms.dom_of_ty ty (cst::elts);
    nf

  (* follow "normal form" pointers deeply in the term *)
  let deref_deep (doms:doms) (t:term) : term =
    let rec aux t =
      let repr = (CC.find t :> term) in
      (* if not already done, traverse all parents to update the functions'
         models *)
      if not (Term.Tbl.mem doms.dom_traversed repr) then (
        Term.Tbl.add doms.dom_traversed repr ();
        Bag.to_seq repr.term_parents |> Sequence.iter aux_ignore;
      );
      (* find a normal form *)
      let nf: term =
        begin match CC.normal_form t with
          | Some (NF_bool true) -> Term.true_
          | Some (NF_bool false) -> Term.false_
          | Some (NF_cstor (cstor, args)) ->
            (* cstor applied to sub-normal forms *)
            Term.app_cst cstor.cstor_cst (IArray.map aux args)
          | None ->
            let repr = (CC.find t :> term) in
            begin match Term.Tbl.get doms.dom_of_class repr with
              | Some u -> u
              | None when Ty.is_uninterpreted t.term_ty ->
                let nf = pick_default ~prefix:"$" doms t.term_ty in
                Term.Tbl.add doms.dom_of_class repr nf;
                nf
              | None ->
                let nf = pick_default ~prefix:"?" doms t.term_ty in
                Term.Tbl.add doms.dom_of_class repr nf;
                nf
            end
        end
      in
      (* update other tables *)
      begin match t.term_cell with
        | True | False -> assert false (* should have normal forms *)
        | Fun _ | DB _ | Mu _
          -> ()
        | Builtin b -> ignore (Term.map_builtin aux b)
        | If (a,b,c) -> aux_ignore a; aux_ignore b; aux_ignore c
        | App_ho (f, l) -> aux_ignore f; List.iter aux_ignore l
        | Case (t, m) -> aux_ignore t; ID.Map.iter (fun _ rhs -> aux_ignore rhs) m
        | App_cst (f, a) when IArray.is_empty a ->
          (* remember [f := c] *)
          Cst.Tbl.replace doms.dom_of_cst f nf
        | App_cst (f, a) ->
          (* remember [f a := c] *)
          let a_values = IArray.map aux a |> IArray.to_list in
          let map =
            Cst.Tbl.get_or ~or_:ValueListMap.empty doms.dom_of_fun f
          in
          Cst.Tbl.replace doms.dom_of_fun f (ValueListMap.add a_values nf map)
      end;
      nf
    and aux_ignore t =
      ignore (aux t)
    in
    aux t

  (* TODO: maybe we really need a notion of "Undefined" that is
           also not a domain element (i.e. equality not defined on it)
           + some syntax for it *)

  (* build the model of a function *)
  let model_of_fun (doms:doms) (c:cst): Ast.term =
    let ty_args, ty_ret = Ty.unfold (Cst.ty c) in
    assert (ty_args <> []);
    let vars =
      List.mapi
        (fun i ty -> Ast.Var.make (ID.makef "x_%d" i) (Conv.ty_to_ast ty))
        ty_args
    in
    let default = match ty_ret.ty_cell with
      | Prop -> Ast.true_ (* should be safe: we would have split it otherwise *)
      | _ ->
        (* TODO: what about other finites types? *)
        pick_default ~prefix:"?" doms ty_ret |> Conv.term_to_ast
    in
    let cases =
      Cst.Tbl.get_or ~or_:ValueListMap.empty doms.dom_of_fun c
      |> ValueListMap.to_list
      |> List.map
        (fun (args,rhs) ->
           assert (List.length ty_args = List.length vars);
           let tests =
             List.map2
               (fun v arg -> Ast.eq (Ast.var v) (Conv.term_to_ast arg))
               vars args
           in
           Ast.and_l tests, Conv.term_to_ast rhs)
    in
    (* decision tree for the body *)
    let body =
      List.fold_left
        (fun else_ (test, then_) -> Ast.if_ test then_ else_)
        default cases
    in
    Ast.fun_l vars body

  let make () : model =
    let env = !model_env_ in
    let doms = create_doms () in
    (* compute values of meta variables *)
    let consts =
      !model_support_
      |> Sequence.of_list
      |> Sequence.filter_map
        (fun c ->
           if Ty.is_arrow (Cst.ty c) then None
           else
             (* find normal form of [c] *)
             let t = Term.const c in
             let t = deref_deep doms t |> Conv.term_to_ast in
             Some (c.cst_id, t))
      |> ID.Map.of_seq
    in
    (* now compute functions (the previous "deref_deep" have updated their use cases)  *)
    let consts =
      !model_support_
      |> Sequence.of_list
      |> Sequence.filter_map
        (fun c ->
           if Ty.is_arrow (Cst.ty c)
           then (
             let t = model_of_fun doms c in
             Some (c.cst_id, t)
           ) else None)
      |> ID.Map.add_seq consts
    in
    (* now we can convert domains *)
    let domains =
      Ty.Tbl.to_seq doms.dom_of_ty
      |> Sequence.filter_map
        (fun (ty,dom) ->
           if Ty.is_uninterpreted ty
           then Some (Conv.ty_to_ast ty, List.rev dom)
           else None)
      |> Ast.Ty.Map.of_seq
    (* and update env: add every domain element to it *)
    and env =
      Ty.Tbl.to_seq doms.dom_of_ty
      |> Sequence.flat_map_l (fun (_,dom) -> dom)
      |> Sequence.fold
        (fun env id -> Ast.env_add_def env id Ast.E_uninterpreted_cst)
        env
    in
    Model.make ~env ~consts ~domains

  let check m =
    Log.debugf 1 (fun k->k "checking model…");
    Log.debugf 5 (fun k->k "(@[<1>candidate model: %a@])" Model.pp m);
    let goals =
      Top_goals.to_seq
      |> Sequence.map Conv.term_to_ast
      |> Sequence.to_list
    in
    Model.check m ~goals
end
   *)

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
  let c = Sat_solver.Clause.make (IArray.to_array_map (Sat_solver.Lit.make sat) c) in
  Sat_solver.add_clause ~permanent:false sat c

let[@inline] assume_eq self t u expl : unit =
  Congruence_closure.assert_eq (cc self) t u (E_lit expl)

let[@inline] assume_distinct self l expl : unit =
  (* FIXME: custom evaluation instead (register to subterms) *)
  Congruence_closure.assert_distinct (cc self) l (E_lit expl)

(*
type unsat_core = Sat.clause list
   *)

(* TODO: main loop with iterative deepening of the unrolling  limit
   (not the value depth limit) *)
let solve ?on_exit:(_=[]) ?check:(_=true) ~assumptions (self:t) : res =
  let r = Sat_solver.solve ~assumptions (solver self) () in
  match r with
  | Sat_solver.Sat (Dagon_sat.Sat_state _st) ->
    Log.debugf 0 (fun k->k "SAT");
    Unknown U_incomplete (* TODO *)
    (*
    let env = Ast.env_empty in
    let m = Model.make ~env
    Sat m *)
  | Sat_solver.Unsat (Dagon_sat.Unsat_state us) ->
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
