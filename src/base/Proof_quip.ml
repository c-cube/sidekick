
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

  let conv_clause (c:PS.Clause.t) : P.clause lazy_t =
    let lits =
      c.lits
      |> Util.array_to_list_map conv_lit
    in
    lazy (List.map Lazy.force lits)

  (* process a step of the trace *)
  let process_step_ (step: PS.Step.t) : unit =
    let lid = step.id in
    let id = Int32.to_int lid in
    if Util.Int_tbl.mem needed_steps_ id then (
      Log.debugf 1 (fun k->k"(@[proof-quip.process-needed-step@ %a@])" PS.Step.pp step);
      Util.Int_tbl.remove needed_steps_ id;

      (* now process the step *)
      begin match step.view with
        | PS.Step_view.Step_input i ->
          let c = conv_clause i.PS.Step_input.c in
          let name = Printf.sprintf "c%d" id in
          let step = lazy (
            let lazy c = c in
            P.S_step_c {name; res=c; proof=P.assertion_c_l c}
          ) in
          add_top_step step;
          (* refer to the step by name now *)
          L_proofs.add lid (lazy (P.ref_by_name name));

        | PS.Step_view.Step_unsat us -> () (* TODO *)
        | PS.Step_view.Step_rup rup -> () (* TODO *)
        | PS.Step_view.Step_bridge_lit_expr _ -> assert false
        | PS.Step_view.Step_cc cc -> () (* TODO *)
        | PS.Step_view.Step_preprocess _ -> () (* TODO *)
        | PS.Step_view.Step_clause_rw _ -> () (* TODO *)
        | PS.Step_view.Step_bool_tauto _ -> () (* TODO *)
        | PS.Step_view.Step_bool_c _ -> () (* TODO *)
        | PS.Step_view.Step_proof_p1 _ -> () (* TODO *)
        | PS.Step_view.Step_true _ -> () (* TODO *)
        | PS.Step_view.Fun_decl _ -> () (* TODO *)
        | PS.Step_view.Expr_def _ -> () (* TODO *)
        | PS.Step_view.Expr_bool _ -> () (* TODO *)
        | PS.Step_view.Expr_if _ -> () (* TODO *)
        | PS.Step_view.Expr_not _ -> () (* TODO *)
        | PS.Step_view.Expr_eq _ -> () (* TODO *)
        | PS.Step_view.Expr_app _ -> () (* TODO *)

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
