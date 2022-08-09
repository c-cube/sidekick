open Sidekick_core_logic
module View = CC_view

let view_as_cc (t : Term.t) : _ CC_view.t =
  let f, args = Term.unfold_app t in
  match Term.view f, args with
  | _, [ _; t; u ] when T_builtins.is_eq f -> View.Eq (t, u)
  | Term.E_const { Const.c_view = T_builtins.C_ite; _ }, [ _ty; a; b; c ] ->
    View.If (a, b, c)
  | Term.E_const { Const.c_view = T_builtins.C_not; _ }, [ a ] -> View.Not a
  | _ ->
    (match Term.view t with
    | Term.E_app (f, a) -> View.App_ho (f, a)
    | Term.E_const { Const.c_view = T_builtins.C_true; _ } -> View.Bool true
    | Term.E_const { Const.c_view = T_builtins.C_false; _ } -> View.Bool false
    | _ -> View.Opaque t)
