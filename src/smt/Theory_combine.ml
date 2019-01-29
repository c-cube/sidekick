
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

module C_clos = Congruence_closure
open Solver_types

module Proof = struct
  type t = Solver_types.proof
  let default = Proof_default
end

module Form = Lit

type formula = Lit.t
type proof = Proof.t
type conflict = Theory.conflict

type theory_state =
  | Th_state : ('a Theory.t1 * 'a) -> theory_state

(* TODO: first-class module instead *)
type t = {
  tst: Term.state;
  (** state for managing terms *)
  cc: C_clos.t lazy_t;
  (** congruence closure *)
  mutable theories : theory_state list;
  (** Set of theories *)
}

let[@inline] cc t = Lazy.force t.cc
let[@inline] tst t = t.tst
let[@inline] theories (self:t) : theory_state Sequence.t =
  fun k -> List.iter k self.theories

(** {2 Interface with the SAT solver} *)

module Plugin = struct

(* handle a literal assumed by the SAT solver *)
let assert_lits (self:t) acts (lits:Lit.t Sequence.t) : unit =
  Msat.Log.debugf 2
    (fun k->k "(@[<1>@{<green>th_combine.assume_lits@}@ @[%a@]@])" (Fmt.seq Lit.pp) lits);
  (* transmit to theories. *)
  C_clos.assert_lits (cc self) lits;
  C_clos.check (cc self) acts;
  theories self (fun (Th_state ((module Th),st)) -> Th.partial_check st acts lits);
  ()

(* TODO: remove
let with_conflict_catch acts f =
  try
    f ();
  with Exn_conflict lit_set ->
    let conflict_clause = IArray.of_list_map Lit.neg lit_set in
    Msat.Log.debugf 3
      (fun k->k "(@[<1>@{<yellow>th_combine.conflict@}@ :clause %a@])"
          Theory.Clause.pp conflict_clause);
    acts.Msat.acts_raise_conflict (IArray.to_list conflict_clause) Proof.default
   *)

let[@inline] iter_atoms_ acts : _ Sequence.t =
  fun f ->
    acts.Msat.acts_iter_assumptions
      (function
        | Msat.Lit a -> f a
        | Msat.Assign _ -> assert false)

(* propagation from the bool solver *)
let check_ (self:t) (acts:_ Msat.acts) =
  let iter = iter_atoms_ acts in
  (* TODO if Config.progress then print_progress(); *)
  Msat.Log.debugf 5 (fun k->k "(th_combine.assume :len %d)" (Sequence.length iter));
  iter (assume_lit self);
  Congruence_closure.check (cc self) acts

let add_formula (self:t) (lit:Lit.t) =
  let t = Lit.view lit in
  let lazy cc = self.cc in
  let n = C_clos.add cc t in
  Equiv_class.set_field Equiv_class.field_is_literal true n;
  ()

(* propagation from the bool solver *)
let[@inline] partial_check (self:t) (acts:_ Msat.acts) =
  check_ self acts

(* perform final check of the model *)
let final_check (self:t) (acts:_ Msat.acts) : unit =
  (* all formulas in the SAT solver's trail *)
  let iter = iter_atoms_ acts in
  (* final check for CC + each theory *)
  Congruence_closure.check (cc self) acts;
  theories self
    (fun (module Th) -> Th.final_check Th.state iter)

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
let act_propagate acts f guard : unit =
  Msat.Log.debugf 2
    (fun k->k "(@[@{<green>th.propagate@}@ %a@ :guard %a@])"
        Lit.pp f (Util.pp_list Lit.pp) guard);
  let reason = Msat.Consequence (guard,Proof.default) in
  acts.Msat.acts_propagate f reason

(** {2 Interface to Congruence Closure} *)

(* when CC decided to merge [r1] and [r2], notify theories *)
let on_merge_from_cc (self:t) r1 r2 e : unit =
  theories self
    (fun (module Th) -> Th.on_merge Th.state r1 r2 e)

(** {2 Main} *)

(* create a new theory combination *)
let create () : t =
  Log.debug 5 "th_combine.create";
  let rec self = {
    tst=Term.create ~size:1024 ();
    cc = lazy (
      (* lazily tie the knot *)
      let on_merge = on_merge_from_cc self in
      C_clos.create ~on_merge ~size:`Big self.tst;
    );
    theories = [];
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

(* TODO: remove
let act_add_local_axiom self c : unit =
  Log.debugf 5 (fun k->k "(@[<2>th_combine.push_local_lemma@ %a@])" Theory.Clause.pp c);
  A.push_local c Proof.default

(* push one clause into [M], in the current level (not a lemma but
   an axiom) *)
let act_add_persistent_axiom self c : unit =
  Log.debugf 5 (fun k->k "(@[<2>th_combine.push_persistent_lemma@ %a@])" Theory.Clause.pp c);
  let (module A) = self.cdcl_acts in
  A.push_persistent c Proof.default
   *)

let check_invariants (self:t) =
  if Util._CHECK_INVARIANTS then (
    Congruence_closure.check_invariants (cc self);
  )

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

let post_backtrack self =
  C_clos.post_backtrack (cc self);
  theories self (fun (module Th) -> Th.post_backtrack Th.state)
