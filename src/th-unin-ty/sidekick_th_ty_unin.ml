open Sidekick_core
open Sidekick_smt_solver

open struct
  module SI = Solver_internal
end

type ty = Term.t

module type ARG = sig
  val ty_is_unin : ty -> bool
end

module Make (A : ARG) = struct
  open A

  type t = { gensym: Gensym.t }

  let create (tst : Term.store) : t =
    let gensym = Gensym.create tst in
    { gensym }

  let pop_levels (self : t) n = if n > 0 then Gensym.reset self.gensym

  let model_ask_ (self : t) (_solver : SI.t) (_m : Model_builder.t) (t : Term.t)
      : _ option =
    if ty_is_unin (Term.ty t) then (
      let s = Gensym.fresh_term self.gensym ~pre:"@c" (Term.ty t) in
      Some (s, [])
    ) else
      None

  let create_and_setup ~id:_ (solver : SI.t) : t =
    let state = create (SI.tst solver) in
    SI.on_model solver ~ask:(model_ask_ state);
    state

  let theory = Solver.mk_theory ~name:"ty-unin" ~create_and_setup ~pop_levels ()
end

let theory (arg : (module ARG)) : Theory.t =
  let module M = Make ((val arg)) in
  M.theory
