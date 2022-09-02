include Sidekick_smt_solver.Solver

let default_arg =
  (module struct
    let view_as_cc = Term.view_as_cc
  end : Sidekick_smt_solver.Sigs.ARG)

let create_default ?stat ?size ~proof ~theories tst : t =
  create default_arg ?stat ?size ~proof ~theories tst ()
