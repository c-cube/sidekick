open Sidekick_core
module Proof = Sidekick_proof
module Check_res = Sidekick_abstract_solver.Check_res

(** Argument to the solver *)
module type ARG = sig
  val or_l : Term.store -> Term.t list -> Term.t
  (** build a disjunction *)
end

type t = {
  tst: Term.store;
  vst: TVar.store;
  arg: (module ARG);
  stats: Stat.t;
  trail: Trail.t;
  plugins: plugin Vec.t;
  term_to_var: Term_to_var.t;
  mutable last_res: Check_res.t option;
  proof_tracer: Proof.Tracer.t;
}

and plugin_action = t

and plugin =
  | P : {
      st: 'st;
      name: string;
      push_level: 'st -> unit;
      pop_levels: 'st -> int -> unit;
      decide: 'st -> TVar.t -> Value.t option;
      propagate: 'st -> plugin_action -> TVar.t -> Value.t -> unit;
      term_to_var_hooks: 'st -> Term_to_var.hook list;
    }
      -> plugin

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

(* plugins *)

module Plugin = struct
  type t = plugin
  type builder = TVar.store -> t

  let[@inline] name (P p) = p.name

  let make_builder ~name ~create ~push_level ~pop_levels ~decide ~propagate
      ~term_to_var_hooks () : builder =
   fun vst ->
    let st = create vst in
    P { name; st; push_level; pop_levels; decide; propagate; term_to_var_hooks }
end

(* backtracking *)

let n_levels (self : t) : int = Trail.n_levels self.trail

let push_level (self : t) : unit =
  Log.debugf 50 (fun k -> k "(@[cdsat.core.push-level@])");
  Trail.push_level self.trail;
  Vec.iter self.plugins ~f:(fun (P p) -> p.push_level p.st);
  ()

let pop_levels (self : t) n : unit =
  Log.debugf 50 (fun k -> k "(@[cdsat.core.pop-levels %d@])" n);
  if n > 0 then self.last_res <- None;
  Trail.pop_levels self.trail n ~f:(fun v -> TVar.unassign self.vst v);
  Vec.iter self.plugins ~f:(fun (P p) -> p.pop_levels p.st n);
  ()

(* term to var *)

let[@inline] get_term_to_var self = self.term_to_var

let[@inline] term_to_var self t : TVar.t =
  Term_to_var.convert self.term_to_var t

let add_term_to_var_hook self h = Term_to_var.add_hook self.term_to_var h

(* plugins *)

let add_plugin self (pb : Plugin.builder) : unit =
  let (P p as plugin) = pb self.vst in
  Vec.push self.plugins plugin;
  List.iter (add_term_to_var_hook self) (p.term_to_var_hooks p.st)

(* solving *)

let add_ty (_self : t) ~ty:_ : unit = ()

let assign (self : t) (v : TVar.t) ~(value : Value.t) ~level:v_level ~reason :
    unit =
  Log.debugf 50 (fun k ->
      k "(@[cdsat.core.assign@ `%a`@ @[<- %a@]@ :reason %a@])"
        (TVar.pp self.vst) v Value.pp value Reason.pp reason);
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

(* plugin actions *)

module Plugin_action = struct
  type t = plugin_action

  let[@inline] propagate (self : t) var value reason : unit =
    assign self var ~value ~level:(Reason.level reason) ~reason

  let term_to_var = term_to_var
end
