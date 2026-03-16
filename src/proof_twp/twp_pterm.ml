(** Translate Proof.Pterm.t rules to .twp P-lines.

    Maps each sidekick rule name to the corresponding .twp proof step.
    Returns the P-index of the emitted step.
*)

module Proof = Sidekick_proof
open Twp_state

let emit_pterm_rule (st : Twp_state.t) (r : Proof.Pterm.rule_apply) : int =
  match r.Proof.Pterm.rule_name with

  | "sat.input" ->
    (* Input clause assumption.
       lits = the literals of the clause.
       For a single literal: P<n> assume E<lit> *)
    (match r.Proof.Pterm.lit_args with
    | [ lit ] ->
      let e_idx = Twp_term.emit_lit st lit in
      let p = alloc_p st in
      emit_line st (Printf.sprintf "P%d assume E%d" p e_idx);
      p
    | lits ->
      (* Multi-literal input clause: emit each lit as comments, then sorry *)
      let p = alloc_p st in
      List.iter (fun lit ->
        let e_idx = Twp_term.emit_lit st lit in
        emit_line st (Printf.sprintf "# sat.input lit E%d" e_idx)
      ) lits;
      emit_line st (Printf.sprintf "# sat.input multi-literal (sorry) P%d" p);
      emit_line st (Printf.sprintf "P%d assume E%d" p Twp_state.e_false);
      p)

  | "core.lemma-cc" ->
    (* CC conflict lemma: the lits form a conflict clause (tautology by CC).
       Encode as: Q<k> seq [pos_lits] [neg_lits] and P<n> ext cc *)
    let lits = r.Proof.Pterm.lit_args in
    (* Split: positive lits (hyps) vs negative lits (conclusions for CC) *)
    let pos_lits = List.filter Lit.sign lits in
    let neg_lits = List.filter (fun l -> not (Lit.sign l)) lits in
    let pos_e = List.map (Twp_term.emit_lit st) pos_lits in
    let neg_e = List.map (fun l ->
      Twp_term.emit_expr st (Lit.term l)
    ) neg_lits in
    let q = alloc_q st in
    let fmt_e_list es = String.concat " " (List.map (Printf.sprintf "E%d") es) in
    emit_line st
      (Printf.sprintf "Q%d seq [%s] [%s]" q (fmt_e_list pos_e) (fmt_e_list neg_e));
    let p = alloc_p st in
    emit_line st (Printf.sprintf "P%d ext cc" p);
    p

  | "core.r1" | "core.res" ->
    (* Resolution: cut P<a> P<b> *)
    (match r.Proof.Pterm.premises with
    | [ p1; p2 ] ->
      let get_p (s : Proof.Step.id) =
        let s_int = Sidekick_trace.Entry_id.to_int s in
        match Hashtbl.find_opt st.step_tbl s_int with
        | Some n -> n
        | None ->
          let n = alloc_p st in
          emit_line st (Printf.sprintf "# ref step %d not found -> P%d" s_int n);
          emit_line st (Printf.sprintf "P%d assume E%d" n Twp_state.e_false);
          n
      in
      let p1_idx = get_p p1 in
      let p2_idx = get_p p2 in
      let p = alloc_p st in
      emit_line st (Printf.sprintf "P%d cut P%d P%d" p p1_idx p2_idx);
      p
    | _ ->
      let p = alloc_p st in
      emit_line st
        (Printf.sprintf "# core.r1/res: wrong premise count (sorry) P%d" p);
      emit_line st (Printf.sprintf "P%d assume E%d" p Twp_state.e_false);
      p)

  | "sat.rc" ->
    (* SAT redundant clause (RUP).
       premises = list of step_ids for the premise proofs. *)
    let hyp_idxs =
      List.filter_map
        (fun (s : Proof.Step.id) ->
          let s_int = Sidekick_trace.Entry_id.to_int s in
          Hashtbl.find_opt st.step_tbl s_int)
        r.Proof.Pterm.premises
    in
    let fmt_p_list ps = String.concat " " (List.map (Printf.sprintf "P%d") ps) in
    let p = alloc_p st in
    emit_line st
      (Printf.sprintf "P%d ext sk.sat_rup [%s]" p (fmt_p_list hyp_idxs));
    p

  | "core.define-term" ->
    (* new_def E<k> *)
    (match r.Proof.Pterm.term_args with
    | t :: _ ->
      let e_idx = Twp_term.emit_expr st t in
      let p = alloc_p st in
      emit_line st (Printf.sprintf "P%d new_def E%d" p e_idx);
      p
    | [] ->
      let p = alloc_p st in
      emit_line st (Printf.sprintf "# core.define-term: no terms (sorry) P%d" p);
      emit_line st (Printf.sprintf "P%d assume E%d" p Twp_state.e_false);
      p)

  | "core.with-defs" | "core.preprocess" | "core.rw-clause"
  | "core.true" | "core.p1" ->
    (* Sorry-style: emit a dummy step *)
    let p = alloc_p st in
    emit_line st
      (Printf.sprintf "# %s (sorry) P%d" r.Proof.Pterm.rule_name p);
    emit_line st (Printf.sprintf "P%d assume E%d" p Twp_state.e_false);
    p

  | name ->
    (* Unknown rule: sorry *)
    let p = alloc_p st in
    emit_line st (Printf.sprintf "# unknown rule '%s' (sorry) P%d" name p);
    emit_line st (Printf.sprintf "P%d assume E%d" p Twp_state.e_false);
    p

(** Translate a Pterm.t and emit .twp lines.
    Returns the P-index of the outermost proof step. *)
let rec emit_pterm (st : Twp_state.t) (pt : Proof.Pterm.t) : int =
  match pt with
  | Proof.Pterm.P_apply r ->
    emit_pterm_rule st r

  | Proof.Pterm.P_ref step_id ->
    (* Reference to a previously emitted step *)
    let s_int = Sidekick_trace.Entry_id.to_int step_id in
    (match Hashtbl.find_opt st.step_tbl s_int with
    | Some n -> n
    | None ->
      let n = alloc_p st in
      emit_line st (Printf.sprintf "# P_ref step %d not found -> P%d" s_int n);
      emit_line st (Printf.sprintf "P%d assume E%d" n Twp_state.e_false);
      n)

  | Proof.Pterm.P_local local_ref ->
    (* Local ref within a P_let binding; resolved by emit_pterm_with_locals *)
    let n = alloc_p st in
    emit_line st (Printf.sprintf "# P_local s%d (unresolved) -> P%d" local_ref n);
    emit_line st (Printf.sprintf "P%d assume E%d" n Twp_state.e_false);
    n

  | Proof.Pterm.P_let (bindings, body) ->
    (* Process bindings, then process body with the local map *)
    let local_map : (int, int) Hashtbl.t = Hashtbl.create 4 in
    List.iter (fun (local_id, pt_inner) ->
      let p_inner = emit_pterm st pt_inner in
      Hashtbl.add local_map local_id p_inner
    ) bindings;
    emit_pterm_with_locals st body local_map

and emit_pterm_with_locals (st : Twp_state.t) (pt : Proof.Pterm.t)
    (locals : (int, int) Hashtbl.t) : int =
  match pt with
  | Proof.Pterm.P_local local_ref ->
    (match Hashtbl.find_opt locals local_ref with
    | Some n -> n
    | None ->
      let n = alloc_p st in
      emit_line st (Printf.sprintf "# unresolved P_local s%d -> P%d" local_ref n);
      emit_line st (Printf.sprintf "P%d assume E%d" n Twp_state.e_false);
      n)
  | Proof.Pterm.P_apply r ->
    (* For rule_apply within let, we need to resolve premise refs via locals *)
    (* For simplicity, just call the regular handler *)
    emit_pterm_rule st r
  | other -> emit_pterm st other
