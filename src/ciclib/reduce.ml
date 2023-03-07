open Types_
module T = Term

type machine = { hd: T.t; args: T.t list; env: T.t list }

let t_of_machine (m : machine) : T.t =
  T.app_l (T.DB.subst_db_l m.hd m.env) m.args

let rec reduce (m : machine) : machine =
  match T.view m.hd, m.args with
  | E_bound_var v, _ when v.bv_idx < List.length m.env ->
    (* lookup in env *)
    let t' = List.nth m.env v.bv_idx in
    reduce { m with hd = t'; env = [] }
  | E_lam (_, _, _ty_arg, body), arg :: tl_args ->
    (* beta-reduce*)
    let m' = { hd = body; env = arg :: m.env; args = tl_args } in
    reduce m'
  | E_app (f, a), _ ->
    (* push onto m.args *)
    let a = T.DB.subst_db_l a m.env in
    reduce { m with hd = f; args = a :: m.args }
  | (E_bound_var _ | E_type _ | E_const (_, _) | E_lam _ | E_pi _), _ -> m

let beta_reduce (t : T.t) : T.t =
  let hd, args = T.unfold_app t in
  let m = { hd; args; env = [] } in
  reduce m |> t_of_machine
