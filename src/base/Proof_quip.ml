
(* output proof *)
module P = Sidekick_quip.Proof

(* serialized proof trace *)
module PS = Sidekick_base_proof_trace.Proof_ser

type t = P.t

module type CONV_ARG = sig
  val proof : Proof.t
  val unsat : Proof.proof_step
end

module Make_lazy_tbl(T:sig type t end)() = struct
  let lazy_tbl_ : T.t lazy_t Util.Int_tbl.t = Util.Int_tbl.create 32

  (** FInd step by its ID *)
  let find (id:PS.ID.t) : T.t =
    match Util.Int_tbl.get lazy_tbl_ (Int32.to_int id) with
    | Some (lazy p) -> p
    | None ->
      Error.errorf "proof-quip: step `%a` was not reconstructed" PS.ID.pp id

  (** Add entry *)
  let add id (e:T.t lazy_t) =
    assert (not (Util.Int_tbl.mem lazy_tbl_ (Int32.to_int id)));
    Util.Int_tbl.add lazy_tbl_ (Int32.to_int id) e
end

module Conv(X : CONV_ARG) : sig
  val reconstruct : unit -> t
end = struct
  let (!!) = Lazy.force

  (* Steps we need to decode.
     Invariant: the IDs of these steps must be lower than the current processed
     ID (we start from the end) *)
  let needed_steps_ = Util.Int_tbl.create 128

  let add_needed_step (id:PS.ID.t) : unit =
    Util.Int_tbl.replace needed_steps_ (Int32.to_int id) ()

  let unsat_id = Proof.Unsafe_.id_of_proof_step_ X.unsat

  (* start with the unsat step *)
  let () = add_needed_step unsat_id

  (* store reconstructed proofs, but lazily because their dependencies
     (sub-steps, terms, etc.) might not have come up in the reverse stream yet. *)
  module L_proofs = Make_lazy_tbl(struct type t = P.t end)()

  (* store reconstructed terms *)
  module L_terms = Make_lazy_tbl(struct type t = P.term end)()

  (* id -> function symbol *)
  let funs: P.Fun.t Util.Int_tbl.t = Util.Int_tbl.create 32

  let find_fun (f:PS.ID.t) : P.Fun.t =
    try Util.Int_tbl.find funs (Int32.to_int f)
    with Not_found -> Error.errorf "unknown function '%ld'" f

  (* list of toplevel steps, in the final proof order *)
  let top_steps_ : P.composite_step lazy_t list ref = ref []
  let add_top_step s = top_steps_ := s :: !top_steps_

  let conv_lit (lit:PS.Lit.t) : P.Lit.t lazy_t =
    let v = Int32.abs lit in
    add_needed_step v;
    lazy (
      let t = L_terms.find v in
      let sign = lit > Int32.zero in
      (* reconstruct literal *)
      P.Lit.mk sign t
    )

  let conv_lits (lits:PS.Lit.t array) : P.Lit.t list lazy_t =
    let lits =
      lits
      |> Util.array_to_list_map conv_lit
    in
    lazy (List.map Lazy.force lits)

  let conv_clause (c:PS.Clause.t) : P.clause lazy_t = conv_lits c.lits

  let name_clause (id: PS.ID.t) : string = Printf.sprintf "c%ld" id
  let name_term (id: PS.ID.t) : string = Printf.sprintf "t%ld" id

  (* TODO: see if we can allow `(stepc c5 (cl …) (… (@ c5) …))`.
     Namely, the alias `c5 := (cl …)` could be available within its own proof
     so we don't have to print it twice, which is useful for rules like `ccl`
     where it's typically `(stepc c5 (cl …) (ccl (cl …)))` for twice the space.
     *)

  let is_def_ (step:PS.Step.t) =
    match step.view with
    | PS.Step_view.Expr_def _ -> true
    | _ -> false

  (* process a step of the trace *)
  let process_step_ (step: PS.Step.t) : unit =
    let lid = step.id in
    let id = Int32.to_int lid in
    if Util.Int_tbl.mem needed_steps_ id || is_def_ step then (
      Log.debugf 20 (fun k->k"(@[proof-quip.process-needed-step@ %a@])" PS.Step.pp step);
      Util.Int_tbl.remove needed_steps_ id;

      (* now process the step *)
      begin match step.view with
        | PS.Step_view.Step_input i ->
          let c = conv_clause i.PS.Step_input.c in
          let name = name_clause lid in
          let step = lazy (
            P.S_step_c {name; res= !!c; proof=P.assertion_c_l !!c}
          ) in
          add_top_step step;
          (* refer to the step by name now *)
          L_proofs.add lid (lazy (P.ref_by_name name));

        | PS.Step_view.Step_unsat { c=uclause } ->
          let c = [] in
          let name = "unsat" in
          add_needed_step uclause;
          let name_c = name_clause uclause in
          add_top_step (lazy (P.S_step_c{name; res=c; proof=P.ref_by_name name_c}));

        | PS.Step_view.Step_cc { eqns } ->
          let c = conv_lits eqns in
          let name = name_clause lid in
          let step = lazy (
            P.S_step_c {name; res= !!c; proof=P.cc_lemma !!c}
          ) in
          add_top_step  step;
          L_proofs.add lid (lazy (P.ref_by_name name))

        | PS.Step_view.Fun_decl { f } ->
          Util.Int_tbl.add funs id f;

        | PS.Step_view.Expr_eq { lhs; rhs } ->
          add_needed_step lhs;
          add_needed_step rhs;
          let name = name_term lid in
          let step = lazy (
            let lhs = L_terms.find lhs
            and rhs = L_terms.find rhs in
            let t = P.T.eq lhs rhs in
            P.S_define_t_name (name, t)
          ) in
          add_top_step step;
          L_terms.add lid (lazy (P.T.ref name))

        | PS.Step_view.Expr_bool {b} ->
          let t = Lazy.from_val (P.T.bool b) in
          L_terms.add lid t

        | PS.Step_view.Expr_isa {c; arg} ->
          add_needed_step c;
          add_needed_step arg;
          let t = lazy (
            let c = find_fun c in
            let arg = L_terms.find arg in
            P.T.is_a c arg
          ) in
          L_terms.add lid t

        | PS.Step_view.Expr_app { f; args } ->
          add_needed_step f;
          Array.iter add_needed_step args;
          let t = lazy (
            let f = find_fun f in
            let args = Array.map L_terms.find args in
            P.T.app_fun f args
          ) in

          if Array.length args > 0 then (
            (* introduce a name *)
            let name = name_term lid in
            let step = lazy (P.S_define_t_name (name, !!t)) in
            add_top_step step;
            L_terms.add lid (lazy (P.T.ref name))
          ) else (
            L_terms.add lid t
          )

        | PS.Step_view.Expr_def { c; rhs } ->
          add_needed_step c;
          add_needed_step rhs;
          let name = name_clause lid in
          (* add [name := (|- c=rhs) by refl c].
             Make sure we do it first, order in final proof will be reversed. *)
          let step_refl = lazy (
            let c = L_terms.find c in
            let rhs = L_terms.find rhs in
            P.S_step_c {name; res=[P.Lit.eq c rhs]; proof=P.refl c}
          ) in
          add_top_step step_refl;
          (* define [c:=rhs] *)
          let step_def = lazy (
            let c = L_terms.find c in
            let rhs = L_terms.find rhs in
            P.S_define_t (c, rhs)
          ) in
          add_top_step step_def;
          L_proofs.add lid (lazy (P.ref_by_name name));

        | PS.Step_view.Expr_not { f } ->
          add_needed_step f;
          let t = lazy (
            let f = L_terms.find f in
            P.T.not_ f
          ) in
          L_terms.add lid t

        | PS.Step_view.Expr_if _ -> () (* TODO *)

        | PS.Step_view.Step_rup { res; hyps } ->
          let res = conv_clause res in
          Array.iter add_needed_step hyps;
          let name = name_clause lid in
          let step = lazy (
            let hyps = Util.array_to_list_map L_proofs.find hyps in
            P.S_step_c {name; res= !!res; proof=P.rup !!res hyps}
          ) in
          add_top_step step;
          L_proofs.add lid (lazy (P.ref_by_name name));

        | PS.Step_view.Step_clause_rw { c; res; using } ->
          let res = conv_clause res in
          add_needed_step c;
          Array.iter add_needed_step using;
          let name = name_clause lid in

          let step = lazy (
            let c = L_proofs.find c in
            let using = Util.array_to_list_map L_proofs.find using in
            let res = !! res in
            P.S_step_c {name; res; proof=P.Clause_rw {res; c0=c; using}}
          ) in
          add_top_step step;
          L_proofs.add lid (lazy (P.ref_by_name name))

        | PS.Step_view.Step_proof_p1 { rw_with; c } ->
          add_needed_step c;
          add_needed_step rw_with;
          let p = lazy (
            let rw_with = L_proofs.find rw_with in
            let c = L_proofs.find c in
            P.paramod1 rw_with c
          ) in
          L_proofs.add lid p;

        | PS.Step_view.Step_proof_r1 { unit; c } ->
          add_needed_step c;
          add_needed_step unit;
          let p = lazy (
            let unit = L_proofs.find unit in
            let c = L_proofs.find c in
            P.res1 unit c
          ) in
          L_proofs.add lid p;

        | PS.Step_view.Step_proof_res { pivot; c1; c2; } ->
          add_needed_step c1;
          add_needed_step c2;
          add_needed_step pivot;
          let p = lazy (
            let pivot = L_terms.find pivot in
            let c1 = L_proofs.find c2 in
            let c2 = L_proofs.find c2 in
            P.res ~pivot c1 c2
          ) in
          L_proofs.add lid p;

        | PS.Step_view.Step_bool_c { rule; exprs } ->
          Array.iter add_needed_step exprs;
          let p = lazy (
            let exprs = Util.array_to_list_map L_terms.find exprs in
            P.bool_c rule exprs
          ) in
          L_proofs.add lid p;

        | PS.Step_view.Step_preprocess { t; u; using } ->
          let name = name_clause lid in
          add_needed_step t;
          add_needed_step u;
          Array.iter add_needed_step using;

          let step = lazy (
            let t = L_terms.find t
            and u = L_terms.find u in
            let using = Util.array_to_list_map L_proofs.find using in
            let res = [P.Lit.eq t u] in
            P.S_step_c {res; name; proof=P.cc_imply_l using t u}
          ) in
          add_top_step step;
          L_proofs.add lid (lazy (P.ref_by_name name));

        | PS.Step_view.Step_bridge_lit_expr _ -> assert false
        | PS.Step_view.Step_bool_tauto _ -> () (* TODO *)
        | PS.Step_view.Step_true _ -> () (* TODO *)

      end
    )

  let reconstruct_once_ = lazy (
    Profile.with_ "proof-quip.reconstruct" @@ fun () ->
    Proof.iter_steps_backward X.proof process_step_;
    ()
  )

  let reconstruct () : t =
    Lazy.force reconstruct_once_;
    let steps = Util.array_of_list_map Lazy.force !top_steps_ in
    P.composite_a steps
end

let of_proof (self:Proof.t) ~(unsat:Proof.proof_step) : P.t =
  let module C = Conv(struct
      let proof = self
      let unsat = unsat
    end) in
  C.reconstruct()

type out_format = Sidekick_quip.out_format =
  | Sexp
  | CSexp

let output = Sidekick_quip.output
