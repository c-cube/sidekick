open Sidekick_core
module Proof = Sidekick_proof
module Asolver = Sidekick_abstract_solver
module Check_res = Asolver.Check_res
module Plugin_action = Core.Plugin_action
module Plugin = Core.Plugin

module type ARG = sig
  module Core : Core.ARG
  module Bool : Plugin_bool.ARG
  module UF : Plugin_uninterpreted.ARG
end

type t = {
  tst: Term.store;
  vst: TVar.store;
  core: Core.t;
  stats: Stat.t;
  arg: (module ARG);
  proof_tracer: Proof.Tracer.t;
}

let create ?(stats = Stat.create ()) ~(arg : (module ARG)) tst vst ~proof_tracer
    () : t =
  let (module A) = arg in
  let core =
    Core.create ~stats ~arg:(module A.Core : Core.ARG) tst vst ~proof_tracer ()
  in
  Core.add_plugin core (Plugin_bool.builder (module A.Bool : Plugin_bool.ARG));
  Core.add_plugin core
    (Plugin_uninterpreted.builder (module A.UF : Plugin_uninterpreted.ARG));
  { tst; vst; arg; core; stats; proof_tracer }

let[@inline] core self = self.core
let add_plugin self p = Core.add_plugin self.core p
let[@inline] iter_plugins self f = Core.iter_plugins self.core ~f
let[@inline] tst self = self.tst
let[@inline] vst self = self.vst

(* solving *)

let add_ty (_self : t) ~ty:_ : unit = ()

let assert_term_ (self : t) (t : Term.t) pr : unit =
  Log.debugf 50 (fun k -> k "(@[cdsat.core.assert@ %a@])" Term.pp t);
  let sign, t = Term.abs self.tst t in
  let v = Core.term_to_var self.core t in
  match TVar.value self.vst v with
  | None ->
    let pr = Proof.Tracer.add_step self.proof_tracer pr in
    Core.assign self.core v
      ~value:(Term.bool_val self.tst sign)
      ~level:0
      ~reason:(Reason.propagate_l self.vst [] pr)
  | Some value when Term.is_true value && sign -> ()
  | Some value when Term.is_false value && not sign -> ()
  | Some value when Term.is_true value && not sign -> () (* TODO: conflict *)
  | Some value when Term.is_false value && sign -> () (* TODO: conflict *)
  (* TODO: conflict *)
  | Some value ->
    Error.errorf "cdsat.assert@ value for %a@ should be true or false,@ not %a"
      (TVar.pp self.vst) v Value.pp value

let assert_term self t : unit =
  let pr () =
    let lit = Lit.atom self.tst t in
    Proof.Sat_rules.sat_input_clause [ lit ]
  in
  assert_term_ self t pr

let assert_clause (self : t) (lits : Lit.t array) p : unit =
  let (module A) = self.arg in
  (* turn literals into a or-term *)
  let args =
    Util.array_to_list_map
      (fun lit ->
        let t = Lit.term lit in
        if Lit.sign lit then
          t
        else
          Term.not self.tst t)
      lits
  in
  let t = A.Core.or_l self.tst args in
  assert_term_ self t p

let pp_stats out self = Stat.pp out self.stats

let solve ?(on_exit = []) ?(on_progress = ignore)
    ?(should_stop = fun _ -> false) ~assumptions (self : t) : Check_res.t =
  Core.solve self.core ~on_exit ~on_progress ~should_stop ~assumptions

(* asolver interface *)

let as_asolver (self : t) : Asolver.t =
  object (asolver)
    method tst = self.tst
    method assert_clause lits p : unit = assert_clause self lits p

    method assert_clause_l lits p : unit =
      asolver#assert_clause (Array.of_list lits) p

    method add_ty ~ty : unit = add_ty self ~ty
    method lit_of_term ?sign t = Lit.atom ?sign self.tst t
    method assert_term t : unit = assert_term self t
    method last_res = Core.last_res self.core
    method proof_tracer = self.proof_tracer
    method pp_stats out () = pp_stats out self

    method solve ?on_exit ?on_progress ?should_stop ~assumptions ()
        : Check_res.t =
      solve ?on_exit ?on_progress ?should_stop ~assumptions self
  end
