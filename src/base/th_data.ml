(** Theory of datatypes *)

open Sidekick_core

let arg =
  (module struct
    open! Sidekick_th_data
    open Data_ty
    module Cstor = Cstor

    (* TODO: we probably want to make sure cstors are not polymorphic?!
       maybe work on a type/cstor that's applied to pre-selected variables,
       like [Map A B] with [A],[B] used for the whole type *)
    let unfold_pi t =
      let rec unfold acc t =
        match Term.view t with
        | Term.E_pi (_, ty, bod) -> unfold (ty :: acc) bod
        | _ -> List.rev acc, t
      in
      unfold [] t

    let as_datatype ty : _ data_ty_view =
      let args, ret = unfold_pi ty in
      if args <> [] then
        Ty_arrow (args, ret)
      else (
        match Data_ty.as_data ty, Term.view ty with
        | Some d, _ ->
          let cstors = Lazy.force d.data_cstors in
          let cstors = ID.Map.fold (fun _ c l -> c :: l) cstors [] in
          Ty_data { cstors }
        | None, E_app (a, b) -> Ty_other { sub = [ a; b ] }
        | None, E_pi (_, a, b) -> Ty_other { sub = [ a; b ] }
        | ( None,
            ( E_const _ | E_var _ | E_type _ | E_bound_var _ | E_lam _
            | E_app_fold _ ) ) ->
          Ty_other { sub = [] }
      )

    let view_as_data t : _ data_view =
      let h, args = Term.unfold_app t in
      match
        Data_ty.as_cstor h, Data_ty.as_select h, Data_ty.as_is_a h, args
      with
      | Some c, _, _, _ ->
        (* TODO: check arity? store it in [c] ? *)
        T_cstor (c, args)
      | None, Some sel, _, [ arg ] ->
        T_select (sel.select_cstor, sel.select_i, arg)
      | None, None, Some c, [ arg ] -> T_is_a (c, arg)
      | _ -> T_other t

    let mk_eq = Term.eq
    let mk_cstor tst c args : Term.t = Term.app_l tst (Data_ty.cstor tst c) args

    let mk_sel tst c i u =
      Term.app_l tst (Data_ty.select tst @@ Data_ty.Cstor.select_idx c i) [ u ]

    let mk_is_a tst c u : Term.t =
      if c.cstor_arity = 0 then
        Term.eq tst u (Data_ty.cstor tst c)
      else
        Term.app_l tst (Data_ty.is_a tst c) [ u ]

    (* NOTE: maybe finiteness should be part of the core typeclass for
       type consts? or we have a registry for infinite types? *)

    let rec ty_is_finite ty =
      match Term.view ty with
      | E_const { Const.c_view = Uconst.Uconst _; _ } -> true
      | E_const { Const.c_view = Data_ty.Data _d; _ } -> true (* TODO: ?? *)
      | E_pi (_, a, b) -> ty_is_finite a && ty_is_finite b
      | _ -> true

    let ty_set_is_finite _ _ = () (* TODO: remove, use a weak table instead *)
  end : Sidekick_th_data.ARG)

let theory = Sidekick_th_data.make arg
