(** Encode sidekick [Pterm.t] proof steps into minidag nodes.

    Targeting the granite [ext-proof-fmt.json] command vocabulary:
      p.hyp  p.res  p.eq  rs.a  rs.r  eq.u  eq.c  seq  clause

    Sidekick-specific oracle steps use [sk.*] commands:
      sk.cc_conflict  sk.sat_rup  sk.bool_ax  sk.r1  sk.p1
      sk.lra  sk.preprocess  sk.rw-clause  sk.sorry

    Step IDs ([Proof.Step.id] = [Entry_id.t] = int) are the minidag byte
    offset of the corresponding proof node — no separate table needed.
*)

open Sidekick_proof
module E = Sidekick_minidag.Encode
open Term_encoder

type t = {
  te: Term_encoder.t;
  tst: Term.store;
}

let create te tst : t = { te; tst }

let enc self = self.te.enc
let nd self cmd f = E.write_node (enc self) cmd f

(* ---- Helpers ---------------------------------------------------- *)

let encode_term' self = encode_term self.te
let encode_lit' self = encode_lit self.te self.tst

(** [seq self ~hyps ~concls] emits [seq hyp... null concl...] *)
let emit_seq self ~hyps ~concls =
  nd self "seq" (fun e ->
      List.iter (E.ref e) hyps;
      E.null e;
      List.iter (E.ref e) concls)

(** Emit [p.hyp] with the given conclusion offsets and no hypotheses. *)
let emit_hyp self concls =
  let seq = emit_seq self ~hyps:[] ~concls in
  nd self "p.hyp" (fun e -> E.ref e seq)

(** Emit [sk.sorry] with a descriptive message. *)
let emit_sorry self msg =
  nd self "sk.sorry" (fun e -> E.string e msg)

(** Convert a step id (= byte offset stored as int) back to an [E.offset]. *)
let step_off (_self : t) (sid : Step.id) : E.offset =
  E.offset_of_int (Sidekick_trace.Entry_id.to_int sid)

(* ---- Rule handlers ---------------------------------------------- *)

let emit_hyp_lits self lits =
  emit_hyp self (List.map (encode_lit' self) lits)

(** Binary resolution: emit as [sk.r1] oracle (trusted by the checker). *)
let emit_resolution self ~pivot ~p1 ~p2 =
  nd self "sk.r1" (fun e -> E.ref e p1; E.ref e p2; E.ref e pivot)

(** RUP (redundant by unit propagation): oracle step referencing all hyp proofs. *)
let emit_sat_rup self hyp_sids =
  let dag_offs = List.map (step_off self) hyp_sids in
  nd self "sk.sat_rup" (fun e -> List.iter (E.ref e) dag_offs)

(** CC conflict: oracle step referencing all conflicting lits. *)
let emit_cc_conflict self lits =
  let lit_offs = List.map (encode_lit' self) lits in
  nd self "sk.cc_conflict" (fun e -> List.iter (E.ref e) lit_offs)

(** Boolean axiom: any [bool.*] rule name. *)
let emit_bool_ax self name term_args =
  let term_offs = List.map (encode_term' self) term_args in
  nd self "sk.bool_ax" (fun e ->
      E.string e name;
      List.iter (E.ref e) term_offs)

(* ---- Main dispatch ---------------------------------------------- *)

let rec encode_rule self (r : Pterm.rule_apply) : E.offset =
  let { Pterm.rule_name; lit_args; term_args; premises; _ } = r in
  match rule_name with

  | "sat.input" ->
    emit_hyp_lits self lit_args

  | "sat.rc" ->
    (* RUP redundant clause *)
    (match premises with
     | [] -> emit_hyp_lits self lit_args
     | _  -> emit_sat_rup self premises)

  | "core.res" ->
    (match premises, term_args with
     | [p1; p2], [pivot] ->
       emit_resolution self
         ~pivot:(encode_term' self pivot)
         ~p1:(step_off self p1) ~p2:(step_off self p2)
     | [p1; p2], [] ->
       let o1 = step_off self p1 and o2 = step_off self p2 in
       nd self "sk.sorry" (fun e ->
           E.string e "core.res: no pivot"; E.ref e o1; E.ref e o2)
     | _ -> emit_sorry self "core.res: bad args")

  | "core.r1" ->
    (match premises with
     | [p1; p2] ->
       let o1 = step_off self p1 and o2 = step_off self p2 in
       nd self "sk.r1" (fun e -> E.ref e o1; E.ref e o2)
     | _ -> emit_sorry self "core.r1: bad args")

  | "core.p1" ->
    (match premises with
     | [p1; p2] ->
       let o1 = step_off self p1 and o2 = step_off self p2 in
       nd self "sk.p1" (fun e -> E.ref e o1; E.ref e o2)
     | _ -> emit_sorry self "core.p1: bad args")

  | "core.lemma-cc" ->
    emit_cc_conflict self lit_args

  | "core.define-term" ->
    (match term_args with
     | [c; rhs] -> emit_hyp self [encode_term' self (Term.eq self.tst c rhs)]
     | _ -> emit_sorry self "core.define-term: bad args")

  | "core.preprocess" ->
    let prem_offs = List.map (step_off self) premises in
    nd self "sk.preprocess" (fun e -> List.iter (E.ref e) prem_offs)

  | "core.with-defs" ->
    (match premises with
     | p :: _ -> step_off self p
     | []     -> emit_sorry self "core.with-defs: no premises")

  | "core.rw-clause" ->
    let prem_offs = List.map (step_off self) premises in
    let lit_offs = List.map (encode_lit' self) lit_args in
    nd self "sk.rw-clause" (fun e ->
        List.iter (E.ref e) prem_offs;
        E.null e;
        List.iter (E.ref e) lit_offs)

  | "core.true" ->
    emit_hyp self [encode_term' self (Term.true_ self.tst)]

  | "lra.lemma" ->
    let lit_offs = List.map (encode_lit' self) lit_args in
    nd self "sk.lra" (fun e -> List.iter (E.ref e) lit_offs)

  | name when String.length name >= 5
           && String.sub name 0 5 = "bool." ->
    emit_bool_ax self name term_args

  | name ->
    let prem_offs = List.map (step_off self) premises in
    let term_offs = List.map (encode_term' self) term_args in
    nd self "sk.sorry" (fun e ->
        E.string e name;
        List.iter (E.ref e) prem_offs;
        List.iter (E.ref e) term_offs)

and encode_pterm self (pt : Pterm.t) : E.offset =
  match pt with
  | Pterm.P_ref sid -> step_off self sid
  | Pterm.P_apply r -> encode_rule self r


(** Emit a proof step and return its minidag offset (= the new step id). *)
let emit_step self (_sid : Step.id) (pt : Pterm.delayed) : E.offset =
  encode_pterm self (pt ())
