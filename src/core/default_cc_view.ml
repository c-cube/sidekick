open Sidekick_core_logic
module View = CC_view

let view_as_cc (t : Term.t) : _ CC_view.t =
  let f, args = Term.unfold_app t in
  match Term.view f, args with
  | Term.E_const { Const.c_view = T_builtins.C_eq; _ }, [ _; t; u ] ->
    View.Eq (t, u)
  | Term.E_const { Const.c_view = T_builtins.C_ite; _ }, [ _ty; a; b; c ] ->
    View.If (a, b, c)
  | Term.E_const { Const.c_view = T_builtins.C_not; _ }, [ a ] -> View.Not a
  | Term.E_const { Const.c_ops = (module OP); c_view; _ }, _
    when OP.opaque_to_cc c_view ->
    (* this constant hides its arguments *)
    View.Opaque t
  | _ ->
    (match Term.view t with
    | Term.E_app (f, a) -> View.App_ho (f, a)
    | Term.E_const { Const.c_view = T_builtins.C_true; _ } -> View.Bool true
    | Term.E_const { Const.c_view = T_builtins.C_false; _ } -> View.Bool false
    | Term.E_app_fold _ -> View.Opaque t
    | _ -> View.Opaque t)
