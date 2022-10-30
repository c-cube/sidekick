open Sidekick_core
module Proof = Sidekick_proof
module Asolver = Sidekick_abstract_solver
module Check_res = Asolver.Check_res

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
  }

  let make ~name ~push_level ~pop_levels ~decide ~propagate () : t =
    { name; push_level; pop_levels; decide; propagate }
end

type t = {
  tst: Term.store;
  vst: TVar.store;
  stats: Stat.t;
  trail: Trail.t;
  plugins: Plugin.t Vec.t;
  mutable last_res: Check_res.t option;
  proof_tracer: Proof.Tracer.t;
}

let create ?(stats = Stat.create ()) tst vst ~proof_tracer () : t =
  {
    tst;
    vst;
    stats;
    trail = Trail.create ();
    plugins = Vec.create ();
    last_res = None;
    proof_tracer;
  }

let[@inline] trail self = self.trail
let add_plugin self p = Vec.push self.plugins p
let[@inline] iter_plugins self f = Vec.iter ~f self.plugins
let[@inline] tst self = self.tst
let[@inline] vst self = self.vst

(* solving *)

let add_ty (_self : t) ~ty:_ : unit = ()
let assert_clause (self : t) lits p : unit = assert false
let assert_term (self : t) t : unit = assert false
let pp_stats out self = Stat.pp out self.stats

let solve ?on_exit ?on_progress ?should_stop ~assumptions (self : t) :
    Check_res.t =
  assert false

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
    method last_res = self.last_res
    method proof_tracer = self.proof_tracer
    method pp_stats out () = pp_stats out self

    method solve ?on_exit ?on_progress ?should_stop ~assumptions ()
        : Check_res.t =
      solve ?on_exit ?on_progress ?should_stop ~assumptions self
  end
