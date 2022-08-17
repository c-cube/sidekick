open Sidekick_core_logic

type term = Sidekick_core_logic.Term.t

type hook = recurse:term Fmt.printer -> Fmt.t -> term -> bool
(** Printing hook, responsible for printing certain subterms *)

module Hooks = struct
  type t = hook list

  let empty = []
  let add h l = h :: l
end

let pp_builtins_ : hook =
 fun ~recurse out t ->
  match Default_cc_view.view_as_cc t with
  | CC_view.If (a, b, c) ->
    Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" recurse a recurse b recurse c;
    true
  | CC_view.Eq (a, b) ->
    Fmt.fprintf out "(@[=@ %a@ %a@])" recurse a recurse b;
    true
  | _ -> false

let default_ : Hooks.t = Hooks.(empty |> add pp_builtins_)
let default_hooks = ref default_

(* debug printer *)
let expr_pp_with_ ~max_depth ~hooks out (e : term) : unit =
  let open Term in
  let rec loop k ~depth names out e =
    let pp' = loop k ~depth:(depth + 1) names in

    let hook_fired = List.exists (fun h -> h ~recurse:pp' out e) hooks in
    if not hook_fired then (
      match Term.view e with
      | E_type 0 -> Fmt.string out "Type"
      | E_type i -> Fmt.fprintf out "Type(%d)" i
      | E_var v -> Fmt.string out (Var.name v)
      (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
      | E_bound_var v ->
        let idx = v.Bvar.bv_idx in
        (match CCList.nth_opt names idx with
        | Some n when n <> "" -> Fmt.fprintf out "%s[%d]" n idx
        | _ -> Fmt.fprintf out "_[%d]" idx)
      | E_const c -> Const.pp out c
      | (E_app _ | E_lam _) when depth > max_depth -> Fmt.fprintf out "@<1>…"
      | E_app _ ->
        let f, args = unfold_app e in
        Fmt.fprintf out "(%a@ %a)" pp' f (Util.pp_list pp') args
      | E_lam ("", _ty, bod) ->
        Fmt.fprintf out "(@[\\_:@[%a@].@ %a@])" pp' _ty
          (loop (k + 1) ~depth:(depth + 1) ("" :: names))
          bod
      | E_lam (n, _ty, bod) ->
        Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp' _ty
          (loop (k + 1) ~depth:(depth + 1) (n :: names))
          bod
      | E_pi (_, ty, bod) when is_closed bod ->
        (* actually just an arrow *)
        Fmt.fprintf out "(@[%a@ -> %a@])"
          (loop k ~depth:(depth + 1) names)
          ty
          (loop (k + 1) ~depth:(depth + 1) ("" :: names))
          bod
      | E_pi ("", _ty, bod) ->
        Fmt.fprintf out "(@[Pi _:@[%a@].@ %a@])" pp' _ty
          (loop (k + 1) ~depth:(depth + 1) ("" :: names))
          bod
      | E_pi (n, _ty, bod) ->
        Fmt.fprintf out "(@[Pi %s:@[%a@].@ %a@])" n pp' _ty
          (loop (k + 1) ~depth:(depth + 1) (n :: names))
          bod
    )
  in
  Fmt.fprintf out "@[%a@]" (loop 0 ~depth:0 []) e

let pp_with hooks out e : unit = expr_pp_with_ ~max_depth:max_int ~hooks out e
let pp out e = pp_with !default_hooks out e
