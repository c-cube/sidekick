
(** {1 Main theory} *)

(** Combine the congruence closure with a number of plugins *)

open Solver_types

module Proof = struct
  type t = Solver_types.proof
  let default = Proof_default
end

module Formula = Lit
module Eq_class = CC.N
module Expl = CC.Expl

type formula = Lit.t
type proof = Proof.t
type conflict = Theory.conflict

type theory_state =
  | Th_state : ('a Theory.t1 * 'a) -> theory_state

(* TODO: first-class module instead *)
type t = {
  tst: Term.state;
  (** state for managing terms *)
  cc: CC.t lazy_t;
  (** congruence closure *)
  mutable theories : theory_state list;
  (** Set of theories *)
}

let[@inline] cc (t:t) = Lazy.force t.cc
let[@inline] tst t = t.tst
let[@inline] theories (self:t) : theory_state Iter.t =
  fun k -> List.iter k self.theories

(** {2 Interface with the SAT solver} *)

(* handle a literal assumed by the SAT solver *)
let assert_lits_ ~final (self:t) acts (lits:Lit.t Iter.t) : unit =
  Msat.Log.debugf 2
    (fun k->k "(@[<hv1>@{<green>th_combine.assume_lits@}%s@ %a@])"
        (if final then "[final]" else "") (Util.pp_seq ~sep:"; " Lit.pp) lits);
  (* transmit to CC *)
  let cc = cc self in
  if not final then (
    CC.assert_lits cc lits;
  );
  (* transmit to theories. *)
  CC.check cc acts;
  let module A = struct
    let cc = cc
    let[@inline] raise_conflict c : 'a = acts.Msat.acts_raise_conflict c Proof_default
    let[@inline] propagate p cs : unit =
      acts.Msat.acts_propagate p (Msat.Consequence (fun () -> cs(), Proof_default))
    let[@inline] propagate_l p cs : unit = propagate p (fun()->cs)
    let[@inline] add_local_axiom lits : unit =
      acts.Msat.acts_add_clause ~keep:false lits Proof_default
    let[@inline] add_persistent_axiom lits : unit =
      acts.Msat.acts_add_clause ~keep:true lits Proof_default
    let[@inline] add_lit lit : unit = acts.Msat.acts_mk_lit lit
  end in
  let acts = (module A : Theory.ACTIONS) in
  theories self
    (fun (Th_state ((module Th),st)) ->
       (* give new merges, then call {final,partial}-check *)
       if final then Th.final_check st acts lits else Th.partial_check st acts lits);
  ()

let[@inline] iter_atoms_ acts : _ Iter.t =
  fun f ->
    acts.Msat.acts_iter_assumptions
      (function
        | Msat.Lit a -> f a
        | Msat.Assign _ -> assert false)

(* propagation from the bool solver *)
let check_ ~final (self:t) (acts:_ Msat.acts) =
  let iter = iter_atoms_ acts in
  (* TODO if Config.progress then print_progress(); *)
  Msat.Log.debugf 5 (fun k->k "(th_combine.assume :len %d)" (Iter.length iter));
  assert_lits_ ~final self acts iter

let add_formula (self:t) (lit:Lit.t) =
  let t = Lit.term lit in
  let lazy cc = self.cc in
  let n = CC.add_term cc t in
  CC.set_as_lit cc n (Lit.abs lit);
  ()

(* propagation from the bool solver *)
let[@inline] partial_check (self:t) (acts:_ Msat.acts) : unit =
  check_ ~final:false self acts

(* perform final check of the model *)
let[@inline] final_check (self:t) (acts:_ Msat.acts) : unit =
  check_ ~final:true self acts

let push_level (self:t) : unit =
  CC.push_level (cc self);
  theories self (fun (Th_state ((module Th), st)) -> Th.push_level st)

let pop_levels (self:t) n : unit =
  CC.pop_levels (cc self) n;
  theories self (fun (Th_state ((module Th), st)) -> Th.pop_levels st n)

let mk_model (self:t) lits : Model.t =
  let m =
    Iter.fold
      (fun m (Th_state ((module Th),st)) -> Th.mk_model st lits m)
      Model.empty (theories self)
  in
  (* now complete model using CC *)
  CC.mk_model (cc self) m

(** {2 Interface to Congruence Closure} *)

(** {2 Main} *)

(* create a new theory combination *)
let create () : t =
  Log.debug 5 "th_combine.create";
  let rec self = {
    tst=Term.create ~size:1024 ();
    cc = lazy (
      (* lazily tie the knot *)
      (* TODO: pass theories *)
      CC.create ~size:`Big self.tst;
    );
    theories = [];
  } in
  ignore (Lazy.force @@ self.cc : CC.t);
  self

let check_invariants (self:t) =
  if Util._CHECK_INVARIANTS then (
    CC.check_invariants (cc self);
  )

let add_theory (self:t) (th:Theory.t) : unit =
let (module Th) = th in
  Log.debugf 2
    (fun k-> k "(@[th_combine.add_th@ :name %S@])" Th.name);
  let st = Th.create self.tst in
  (* re-pack as a [Theory.t1] *)
  self.theories <- (Th_state ((module Th),st)) :: self.theories

let add_theory_l self = List.iter (add_theory self)
