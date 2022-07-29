open Sidekick_core
module View = View

module type ARG = Sigs.ARG
module type S = Sigs.S
module type DYN_MONOID_PLUGIN = Sigs.DYN_MONOID_PLUGIN
module type MONOID_PLUGIN_ARG = Sigs.MONOID_PLUGIN_ARG
module type MONOID_PLUGIN_BUILDER = Sigs.MONOID_PLUGIN_BUILDER

module Make (A : ARG) : S = Core_cc.Make (A)

module Base : S = Make (struct
  let view_as_cc (t : Term.t) : _ View.t =
    let f, args = Term.unfold_app t in
    match Term.view f, args with
    | _, [ _; t; u ] when Term.is_eq f -> View.Eq (t, u)
    | _ ->
      (match Term.view t with
      | Term.E_app (f, a) -> View.App_ho (f, a)
      | Term.E_const c -> View.App_fun (c, Iter.empty)
      | _ -> View.Opaque t)
end)
