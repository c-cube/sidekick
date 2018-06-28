
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

module Sat_solver = Sidekick_sat
module C_clos = Congruence_closure
open Solver_types

module Proof = struct
  type t = Proof
  let default = Proof
end

module Form = Lit

type formula = Lit.t
type proof = Proof.t
type conflict = Theory.conflict

(* raise upon conflict *)
exception Exn_conflict of conflict

(* TODO: first-class module instead *)
type t = {
  cdcl_acts: (formula,proof) Sat_solver.actions;
  (** actions provided by the SAT solver *)
  tst: Term.state;
  (** state for managing terms *)
  cc: C_clos.t lazy_t;
  (** congruence closure *)
  mutable theories : Theory.state list;
  (** Set of theories *)
  mutable conflict: conflict option;
  (** current conflict, if any *)
}

let[@inline] cc t = Lazy.force t.cc
let[@inline] tst t = t.tst
let[@inline] theories (self:t) : Theory.state Sequence.t =
  fun k -> List.iter k self.theories

(** {2 Interface with the SAT solver} *)

(* handle a literal assumed by the SAT solver *)
let assume_lit (self:t) (lit:Lit.t) : unit =
  Sat_solver.Log.debugf 2
    (fun k->k "(@[<1>@{<green>th_combine.assume_lit@}@ @[%a@]@])" Lit.pp lit);
  (* check consistency first *)
  begin match Lit.view lit with
    | {term_view=Bool true; _} -> ()
    | {term_view=Bool false; _} -> ()
    | _ ->
      (* transmit to theories. *)
      C_clos.assert_lit (cc self) lit;
      theories self (fun (module Th) -> Th.on_assert Th.state lit);
  end

(* return result to the SAT solver *)
let cdcl_return_res (self:t) : _ Sat_solver.res =
  begin match self.conflict with
    | None ->
      Sat_solver.Sat
    | Some lit_set ->
      let conflict_clause = IArray.of_list_map Lit.neg lit_set in
      Sat_solver.Log.debugf 3
        (fun k->k "(@[<1>@{<yellow>th_combine.conflict@}@ :clause %a@])"
            Theory.Clause.pp conflict_clause);
      self.conflict <- None;
      Sat_solver.Unsat (IArray.to_list conflict_clause, Proof.default)
  end

let with_conflict_catch self f =
  begin
    try
      f ()
    with Exn_conflict c ->
      assert (CCOpt.is_none self.conflict);
      self.conflict <- Some c;
  end;
  cdcl_return_res self

(* propagation from the bool solver *)
let assume_real (self:t) (slice:Lit.t Sat_solver.slice_actions) =
  (* TODO if Config.progress then print_progress(); *)
  let (module SA) = slice in
  Log.debugf 5 (fun k->k "(th_combine.assume :len %d)" (Sequence.length @@ SA.slice_iter));
  with_conflict_catch self
    (fun () -> SA.slice_iter (assume_lit self))

let add_formula (self:t) (lit:Lit.t) =
  let t = Lit.view lit in
  let lazy cc = self.cc in
  ignore (C_clos.add cc t : cc_node)

(* propagation from the bool solver *)
let assume (self:t) (slice:_ Sat_solver.slice_actions) =
  match self.conflict with
  | Some _ -> cdcl_return_res self (* already in conflict! *)
  | None -> assume_real self slice

(* perform final check of the model *)
let if_sat (self:t) (slice:Lit.t Sat_solver.slice_actions) : _ Sat_solver.res =
  (* all formulas in the SAT solver's trail *)
  let (module SA) = slice in
  with_conflict_catch self
    (fun () ->
       (* final check for CC + each theory *)
       C_clos.final_check (cc self);
       theories self
         (fun (module Th) -> Th.final_check Th.state SA.slice_iter))

let mk_model (self:t) lits : Model.t =
  let m =
    Sequence.fold
      (fun m (module Th : Theory.STATE) -> Model.merge m (Th.mk_model Th.state lits))
      Model.empty (theories self)
  in
  (* now complete model using CC *)
  Congruence_closure.mk_model (cc self) m

(** {2 Various helpers} *)

(* forward propagations from CC or theories directly to the SMT core *)
let act_propagate (self:t) f guard : unit =
  let (module A) = self.cdcl_acts in
  Sat_solver.Log.debugf 2
    (fun k->k "(@[@{<green>th.propagate@}@ %a@ :guard %a@])"
        Lit.pp f (Util.pp_list Lit.pp) guard);
  A.propagate f guard Proof.default

(** {2 Interface to Congruence Closure} *)

let act_raise_conflict e = raise (Exn_conflict e)

(* when CC decided to merge [r1] and [r2], notify theories *)
let on_merge_from_cc (self:t) r1 r2 e : unit =
  theories self
    (fun (module Th) -> Th.on_merge Th.state r1 r2 e)

let mk_cc_actions (self:t) : C_clos.actions =
  let (module A) = self.cdcl_acts in
  let module R = struct
    let on_backtrack = A.on_backtrack
    let on_merge = on_merge_from_cc self
    let raise_conflict = act_raise_conflict
    let propagate = act_propagate self
  end in
  (module R)

(** {2 Main} *)

(* create a new theory combination *)
let create (cdcl_acts:_ Sat_solver.actions) : t =
  Sat_solver.Log.debug 5 "th_combine.create";
  let rec self = {
    cdcl_acts;
    tst=Term.create ~size:1024 ();
    cc = lazy (
      (* lazily tie the knot *)
      let actions = mk_cc_actions self in
      C_clos.create ~size:1024 ~actions self.tst;
    );
    theories = [];
    conflict = None;
  } in
  ignore (Lazy.force @@ self.cc : C_clos.t);
  self

(** {2 Interface to individual theories} *)

let act_all_classes self = C_clos.all_classes (cc self)

let act_propagate_eq self t u guard =
  C_clos.assert_eq (cc self) t u guard

let act_propagate_distinct self l ~neq guard =
  C_clos.assert_distinct (cc self) l ~neq guard

let act_find self t =
  C_clos.add (cc self) t
  |> C_clos.find (cc self)

let act_add_local_axiom self c : unit =
  Sat_solver.Log.debugf 5 (fun k->k "(@[<2>th_combine.push_local_lemma@ %a@])" Theory.Clause.pp c);
  let (module A) = self.cdcl_acts in
  A.push_local c Proof.default

(* push one clause into [M], in the current level (not a lemma but
   an axiom) *)
let act_add_persistent_axiom self c : unit =
  Sat_solver.Log.debugf 5 (fun k->k "(@[<2>th_combine.push_persistent_lemma@ %a@])" Theory.Clause.pp c);
  let (module A) = self.cdcl_acts in
  A.push_persistent c Proof.default

let mk_theory_actions (self:t) : Theory.actions =
  let (module A) = self.cdcl_acts in
  let module R = struct
    let on_backtrack = A.on_backtrack
    let raise_conflict = act_raise_conflict
    let propagate = act_propagate self
    let all_classes = act_all_classes self
    let propagate_eq = act_propagate_eq self
    let propagate_distinct = act_propagate_distinct self
    let add_local_axiom = act_add_local_axiom self
    let add_persistent_axiom = act_add_persistent_axiom self
    let find = act_find self
  end
  in (module R)

let add_theory (self:t) (th:Theory.t) : unit =
  Sat_solver.Log.debugf 2
    (fun k->k "(@[th_combine.add_th@ :name %S@])" th.Theory.name);
  let th_s = th.Theory.make self.tst (mk_theory_actions self) in
  self.theories <- th_s :: self.theories

let add_theory_l self = List.iter (add_theory self)
