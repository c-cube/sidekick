(** Theory of uninterpreted functions *)

open Sidekick_core
open Sidekick_smt_solver

open struct
  module SI = Solver_internal

  let on_is_subterm ~th_id (solver : SI.t) (_, _, t) : _ list =
    let f, args = Term.unfold_app t in
    (match Term.view f, args with
    | Term.E_const { Const.c_view = Uconst.Uconst _; _ }, _ :: _ ->
      SI.claim_term solver ~th_id t
    | _ -> ());

    []
end

let theory : Theory.t =
  Theory.make ~name:"uf"
    ~create_and_setup:(fun ~id:th_id solver ->
      SI.on_cc_is_subterm solver (on_is_subterm ~th_id solver);
      ())
    ()
