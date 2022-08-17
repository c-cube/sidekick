(** Reducing boolean formulas to clauses *)

let k_config : [ `Dyn | `Static ] Config.Key.t = Config.Key.create ()

let theory_static : Solver.theory =
  Sidekick_th_bool_static.theory
    (module struct
      let view_as_bool = Form.view
      let mk_bool = Form.mk_of_view
    end : Sidekick_th_bool_static.ARG)

let theory_dyn : Solver.theory =
  Sidekick_th_bool_dyn.theory
    (module struct
      let view_as_bool = Form.view
      let mk_bool = Form.mk_of_view
    end : Sidekick_th_bool_static.ARG)

let theory (conf : Config.t) : Solver.theory =
  match Config.find k_config conf with
  | Some `Dyn -> theory_dyn
  | Some `Static -> theory_static
  | None ->
    (* default *)
    theory_static
