let theory : Solver.theory =
  Sidekick_th_ty_unin.theory
    (module struct
      let ty_is_unin = Ty.is_uninterpreted
    end : Sidekick_th_ty_unin.ARG)
