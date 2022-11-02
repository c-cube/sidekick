open Sidekick_core
module Proof = Sidekick_proof
module Check_res = Sidekick_abstract_solver.Check_res

(** Argument to the solver *)
module type ARG = sig
  val or_l : Term.store -> Term.t list -> Term.t
  (** build a disjunction *)
end

module Plugin_action = struct
  type t = { propagate: TVar.t -> Value.t -> Reason.t -> unit }

  let propagate (self : t) var v reas : unit = self.propagate var v reas
end

(** Core plugin *)
module Plugin = struct
  type t = {
    name: string;
    push_level: unit -> unit;
    pop_levels: int -> unit;
    decide: TVar.t -> Value.t option;
    propagate: Plugin_action.t -> TVar.t -> Value.t -> unit;
    term_to_var_hooks: Term_to_var.hook list;
  }

  let make ~name ~push_level ~pop_levels ~decide ~propagate ~term_to_var_hooks
      () : t =
    { name; push_level; pop_levels; decide; propagate; term_to_var_hooks }
end

type t = {
  tst: Term.store;
  vst: TVar.store;
  arg: (module ARG);
  stats: Stat.t;
  trail: Trail.t;
  plugins: Plugin.t Vec.t;
  term_to_var: Term_to_var.t;
  mutable last_res: Check_res.t option;
  proof_tracer: Proof.Tracer.t;
}

let create ?(stats = Stat.create ()) ~arg tst vst ~proof_tracer () : t =
  {
    tst;
    vst;
    arg;
    stats;
    trail = Trail.create ();
    plugins = Vec.create ();
    term_to_var = Term_to_var.create vst;
    last_res = None;
    proof_tracer;
  }

let[@inline] trail self = self.trail
let[@inline] iter_plugins self f = Vec.iter ~f self.plugins
let[@inline] tst self = self.tst
let[@inline] vst self = self.vst
let[@inline] last_res self = self.last_res

(* backtracking *)

let n_levels (self : t) : int = Trail.n_levels self.trail

let push_level (self : t) : unit =
  Log.debugf 50 (fun k -> k "(@[cdsat.core.push-level@])");
  Trail.push_level self.trail;
  Vec.iter self.plugins ~f:(fun (p : Plugin.t) -> p.push_level ());
  ()

let pop_levels (self : t) n : unit =
  Log.debugf 50 (fun k -> k "(@[cdsat.core.pop-levels %d@])" n);
  if n > 0 then self.last_res <- None;
  Trail.pop_levels self.trail n ~f:(fun v -> TVar.unassign self.vst v);
  Vec.iter self.plugins ~f:(fun (p : Plugin.t) -> p.pop_levels n);
  ()

(* term to var *)

let[@inline] get_term_to_var self = self.term_to_var

let[@inline] term_to_var self t : TVar.t =
  Term_to_var.convert self.term_to_var t

let add_term_to_var_hook self h = Term_to_var.add_hook self.term_to_var h

(* plugins *)

let add_plugin self p =
  Vec.push self.plugins p;
  List.iter (add_term_to_var_hook self) p.term_to_var_hooks

(* solving *)

let add_ty (_self : t) ~ty:_ : unit = ()

let assign (self : t) (v : TVar.t) ~(value : Value.t) ~level:v_level ~reason :
    unit =
  Log.debugf 50 (fun k ->
      k "(@[cdsat.core.assign@ %a@ <- %a@])" (TVar.pp self.vst) v Value.pp value);
  self.last_res <- None;
  match TVar.value self.vst v with
  | None ->
    TVar.assign self.vst v ~value ~level:v_level ~reason;
    Trail.push_assignment self.trail v
  | Some value' when Value.equal value value' -> () (* idempotent *)
  | Some value' ->
    (* TODO: conflict *)
    Log.debugf 0 (fun k -> k "TODO: conflict (incompatible values)");
    ()

let solve ~on_exit ~on_progress ~should_stop ~assumptions (self : t) :
    Check_res.t =
  self.last_res <- None;
  (* TODO: outer loop (propagate; decide)* *)
  (* TODO: propagation loop, involving plugins *)
  assert false
