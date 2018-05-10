
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

module Sat_solver = Sidekick_sat
open Solver_types

module Proof = struct
  type t = Proof
  let default = Proof
end

module Form = Lit

type formula = Lit.t
type proof = Proof.t

type conflict = Lit.Set.t

(* raise upon conflict *)
exception Exn_conflict of conflict

type t = {
  cdcl_acts: (formula,proof) Sat_solver.actions;
  (** actions provided by the SAT solver *)
  tst: Term.state;
  (** state for managing terms *)
  cc: Congruence_closure.t lazy_t;
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
    (fun k->k "(@[<1>@{<green>theory_combine.assume_lit@}@ @[%a@]@])" Lit.pp lit);
  (* check consistency first *)
  begin match Lit.view lit with
    | Lit_fresh _ -> ()
    | Lit_expanded _
    | Lit_atom {term_cell=Bool true; _} -> ()
    | Lit_atom {term_cell=Bool false; _} -> ()
    | Lit_atom _ ->
      (* transmit to theories. *)
      Congruence_closure.assert_lit (cc self) lit;
      theories self (fun (Theory.State th) -> th.on_assert th.st lit);
  end

(* return result to the SAT solver *)
let cdcl_return_res (self:t) : _ Sat_solver.res =
  begin match self.conflict with
    | None ->
      Sat_solver.Sat
    | Some lit_set ->
      let conflict_clause =
        Lit.Set.to_list lit_set
        |> IArray.of_list_map Lit.neg
      in
      Sat_solver.Log.debugf 3
        (fun k->k "(@[<1>conflict@ clause: %a@])"
            Theory.Clause.pp conflict_clause);
      self.conflict <- None;
      Sat_solver.Unsat (IArray.to_list conflict_clause, Proof.default)
  end

let[@inline] check (self:t) : unit =
  Congruence_closure.check (cc self)

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
let assume_real (self:t) (slice:_ Sat_solver.slice_actions) =
  (* TODO if Config.progress then print_progress(); *)
  let Sat_solver.Slice_acts slice = slice in
  Log.debugf 5 (fun k->k "(th_combine.assume :len %d)" (Sequence.length slice.slice_iter));
  with_conflict_catch self
    (fun () ->
       slice.slice_iter (assume_lit self);
       (* now check satisfiability *)
       check self
    )

(* propagation from the bool solver *)
let assume (self:t) (slice:_ Sat_solver.slice_actions) =
  match self.conflict with
  | None -> assume_real self slice
  | Some _ ->
    (* already in conflict! *)
    cdcl_return_res self

(* perform final check of the model *)
let if_sat (self:t) (slice:_) : _ Sat_solver.res =
  Congruence_closure.final_check (cc self);
  (* all formulas in the SAT solver's trail *)
  let forms =
    let Sat_solver.Slice_acts r = slice in
    r.slice_iter
  in
  (* final check for each theory *)
  with_conflict_catch self
    (fun () ->
       theories self
         (fun (Theory.State th) -> th.final_check th.st forms))

(** {2 Various helpers} *)

(* forward propagations from CC or theories directly to the SMT core *)
let act_propagate (self:t) f guard : unit =
  let Sat_solver.Actions r = self.cdcl_acts in
  let guard =
    Congruence_closure.explain_unfold_bag (cc self) guard
    |> Lit.Set.to_list
  in
  Sat_solver.Log.debugf 2
    (fun k->k "(@[@{<green>propagate@}@ %a@ :guard %a@])"
        Lit.pp f (Util.pp_list Lit.pp) guard);
  r.propagate f guard Proof.default

(** {2 Interface to Congruence Closure} *)

let act_raise_conflict e = raise (Exn_conflict e)

(* when CC decided to merge [r1] and [r2], notify theories *)
let on_merge_from_cc (self:t) r1 r2 e : unit =
  theories self
    (fun (Theory.State th) -> th.on_merge th.st r1 r2 e)

let mk_cc_actions (self:t) : Congruence_closure.actions =
  let Sat_solver.Actions r = self.cdcl_acts in
  { Congruence_closure.
    on_backtrack = r.on_backtrack;
    on_merge = on_merge_from_cc self;
    raise_conflict = act_raise_conflict;
    propagate = act_propagate self;
  }

(** {2 Main} *)

(* create a new theory combination *)
let create (cdcl_acts:_ Sat_solver.actions) : t =
  Sat_solver.Log.debug 5 "theory_combine.create";
  let rec self = {
    cdcl_acts;
    tst=Term.create ~size:1024 ();
    cc = lazy (
      (* lazily tie the knot *)
      let actions = mk_cc_actions self in
      Congruence_closure.create ~size:1024 ~actions self.tst;
    );
    theories = [];
    conflict = None;
  } in
  ignore (Lazy.force @@ self.cc : Congruence_closure.t);
  self

(** {2 Interface to individual theories} *)

let act_all_classes self = Congruence_closure.all_classes (cc self)

let act_propagate_eq self t u guard =
  Congruence_closure.assert_eq (cc self) t u guard

let act_propagate_distinct self l ~neq guard =
  Congruence_closure.assert_distinct (cc self) l ~neq guard

let act_find self t =
  Congruence_closure.add (cc self) t
  |> Congruence_closure.find (cc self)

let act_add_local_axiom self c : unit =
  Sat_solver.Log.debugf 5 (fun k->k "(@[<2>th_combine.push_local_lemma@ %a@])" Theory.Clause.pp c);
  let Sat_solver.Actions r = self.cdcl_acts in
  r.push_local c Proof.default

(* push one clause into [M], in the current level (not a lemma but
   an axiom) *)
let act_add_persistent_axiom self c : unit =
  Sat_solver.Log.debugf 5 (fun k->k "(@[<2>th_combine.push_persistent_lemma@ %a@])" Theory.Clause.pp c);
  let Sat_solver.Actions r = self.cdcl_acts in
  r.push_persistent c Proof.default

let mk_theory_actions (self:t) : Theory.actions =
  let Sat_solver.Actions r = self.cdcl_acts in
  { Theory.
    on_backtrack = r.on_backtrack;
    raise_conflict = act_raise_conflict;
    propagate = act_propagate self;
    all_classes = act_all_classes self;
    propagate_eq = act_propagate_eq self;
    propagate_distinct = act_propagate_distinct self;
    add_local_axiom = act_add_local_axiom self;
    add_persistent_axiom = act_add_persistent_axiom self;
    find = act_find self;
  }

let add_theory (self:t) (th:Theory.t) : unit =
  Sat_solver.Log.debugf 2
    (fun k->k "(@[theory_combine.add_th@ :name %S@])" th.Theory.name);
  let th_s = th.Theory.make self.tst (mk_theory_actions self) in
  self.theories <- th_s :: self.theories

let add_theory_l self = List.iter (add_theory self)

