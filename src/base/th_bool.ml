(** Reducing boolean formulas to clauses *)

let theory : Solver.theory =
  Sidekick_th_bool_static.theory
    (module struct
      let view_as_bool = Form.view
      let mk_bool = Form.mk_of_view
    end : Sidekick_th_bool_static.ARG)
