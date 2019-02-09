
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

module C_clos = Congruence_closure
open Solver_types

module Proof = struct
  type t = Solver_types.proof
  let default = Proof_default
end

module Formula = Lit

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
  new_merges: (Eq_class.t * Eq_class.t * explanation) Vec.t;
}

let[@inline] cc (t:t) = Lazy.force t.cc
let[@inline] tst t = t.tst
let[@inline] theories (self:t) : theory_state Sequence.t =
  fun k -> List.iter k self.theories

(** {2 Interface with the SAT solver} *)

(* handle a literal assumed by the SAT solver *)
let assert_lits_ ~final (self:t) acts (lits:Lit.t Sequence.t) : unit =
  Msat.Log.debugf 2
    (fun k->k "(@[<1>@{<green>th_combine.assume_lits@}@ @[%a@]@])" (Fmt.seq Lit.pp) lits);
  (* transmit to CC *)
  Vec.clear self.new_merges;
  let cc = cc self in
  C_clos.assert_lits cc lits;
  (* transmit to theories. *)
  C_clos.check cc acts;
  let module A = struct
    let[@inline] raise_conflict c : 'a = acts.Msat.acts_raise_conflict c Proof_default
    let[@inline] propagate_eq t u expl : unit = C_clos.assert_eq cc t u expl
    let propagate_distinct ts ~neq expl = C_clos.assert_distinct cc ts ~neq expl
    let[@inline] propagate p cs : unit = acts.Msat.acts_propagate p (Msat.Consequence (cs, Proof_default))
    let[@inline] add_local_axiom lits : unit =
      acts.Msat.acts_add_clause ~keep:false lits Proof_default
    let[@inline] add_persistent_axiom lits : unit =
      acts.Msat.acts_add_clause ~keep:true lits Proof_default
    let[@inline] find t = C_clos.find_t cc t
    let all_classes = C_clos.all_classes cc
  end in
  let acts = (module A : Theory.ACTIONS) in
  theories self
    (fun (Th_state ((module Th),st)) ->
       (* give new merges, then call {final,partial}-check *)
       Vec.iter (fun (r1,r2,e) -> Th.on_merge st acts r1 r2 e) self.new_merges;
       if final then Th.final_check st acts lits else Th.partial_check st acts lits);
  ()

let[@inline] iter_atoms_ acts : _ Sequence.t =
  fun f ->
    acts.Msat.acts_iter_assumptions
      (function
        | Msat.Lit a -> f a
        | Msat.Assign _ -> assert false)

(* propagation from the bool solver *)
let check_ ~final (self:t) (acts:_ Msat.acts) =
  let iter = iter_atoms_ acts in
  (* TODO if Config.progress then print_progress(); *)
  Msat.Log.debugf 5 (fun k->k "(th_combine.assume :len %d)" (Sequence.length iter));
  assert_lits_ ~final self acts iter

let add_formula (self:t) (lit:Lit.t) =
  let t = Lit.view lit in
  let lazy cc = self.cc in
  let n = C_clos.add cc t in
  Eq_class.set_field Eq_class.field_is_literal true n;
  ()

(* propagation from the bool solver *)
let[@inline] partial_check (self:t) (acts:_ Msat.acts) : unit =
  check_ ~final:false self acts

(* perform final check of the model *)
let[@inline] final_check (self:t) (acts:_ Msat.acts) : unit =
  check_ ~final:true self acts

let push_level (self:t) : unit =
  C_clos.push_level (cc self);
  theories self (fun (Th_state ((module Th), st)) -> Th.push_level st)

let pop_levels (self:t) n : unit =
  C_clos.pop_levels (cc self) n;
  theories self (fun (Th_state ((module Th), st)) -> Th.pop_levels st n)

let mk_model (self:t) lits : Model.t =
  let m =
    Sequence.fold
      (fun m (Th_state ((module Th),st)) -> Model.merge m (Th.mk_model st lits))
      Model.empty (theories self)
  in
  (* now complete model using CC *)
  Congruence_closure.mk_model (cc self) m

(** {2 Interface to Congruence Closure} *)

(* when CC decided to merge [r1] and [r2], notify theories *)
let[@inline] on_merge_from_cc (self:t) r1 r2 e : unit =
  Vec.push self.new_merges (r1,r2,e)

(** {2 Main} *)

(* create a new theory combination *)
let create () : t =
  Log.debug 5 "th_combine.create";
  let rec self = {
    tst=Term.create ~size:1024 ();
    new_merges=Vec.create();
    cc = lazy (
      (* lazily tie the knot *)
      let on_merge = on_merge_from_cc self in
      C_clos.create ~on_merge ~size:`Big self.tst;
    );
    theories = [];
  } in
  ignore (Lazy.force @@ self.cc : C_clos.t);
  self

let check_invariants (self:t) =
  if Util._CHECK_INVARIANTS then (
    Congruence_closure.check_invariants (cc self);
  )

let add_theory (self:t) (th:Theory.t) : unit =
let (module Th) = th in
  Log.debugf 2
    (fun k-> k "(@[th_combine.add_th@ :name %S@])" Th.name);
  let st = Th.create self.tst in
  (* re-pack as a [Theory.t1] *)
  self.theories <- (Th_state ((module Th),st)) :: self.theories

let add_theory_l self = List.iter (add_theory self)
