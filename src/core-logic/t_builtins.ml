open Types_
open Term

type const_view += C_bool | C_eq | C_ite | C_not | C_true | C_false

let ops : const_ops =
  (module struct
    let equal a b =
      match a, b with
      | C_bool, C_bool
      | C_eq, C_eq
      | C_ite, C_ite
      | C_not, C_not
      | C_true, C_true
      | C_false, C_false ->
        true
      | _ -> false

    let hash = function
      | C_bool -> CCHash.int 167
      | C_eq -> CCHash.int 168
      | C_ite -> CCHash.int 169
      | C_not -> CCHash.int 170
      | C_true -> CCHash.int 171
      | C_false -> CCHash.int 172
      | _ -> assert false

    let pp out = function
      | C_bool -> Fmt.string out "Bool"
      | C_eq -> Fmt.string out "="
      | C_ite -> Fmt.string out "ite"
      | C_not -> Fmt.string out "not"
      | C_true -> Fmt.string out "true"
      | C_false -> Fmt.string out "false"
      | _ -> assert false
  end)

let bool store = const store @@ Const.make C_bool ops ~ty:(type_ store)
let true_ store = const store @@ Const.make C_true ops ~ty:(bool store)
let false_ store = const store @@ Const.make C_false ops ~ty:(bool store)

let bool_val store b =
  if b then
    true_ store
  else
    false_ store

let c_eq store =
  let type_ = type_ store in
  let v = bvar_i store 0 ~ty:type_ in
  let ty =
    DB.pi_db ~var_name:"A" store ~var_ty:type_
    @@ arrow_l store [ v; v ] (bool store)
  in
  const store @@ Const.make C_eq ops ~ty

let c_ite store =
  let type_ = type_ store in
  let v = bvar_i store 0 ~ty:type_ in
  let ty =
    DB.pi_db ~var_name:"A" store ~var_ty:type_
    @@ arrow_l store [ bool store; v; v ] v
  in
  const store @@ Const.make C_eq ops ~ty

let c_not store =
  let b = bool store in
  let ty = arrow store b b in
  const store @@ Const.make C_not ops ~ty

let eq store a b = app_l store (c_eq store) [ ty a; a; b ]
let ite store a b c = app_l store (c_ite store) [ ty b; a; b; c ]
let not store a = app store (c_not store) a

let is_bool t =
  match view t with
  | E_const { c_view = C_bool; _ } -> true
  | _ -> false

let is_eq t =
  match view t with
  | E_const { c_view = C_eq; _ } -> true
  | _ -> false

let rec abs t =
  match view t with
  | E_app ({ view = E_const { c_view = C_not; _ }; _ }, u) ->
    let sign, v = abs u in
    Stdlib.not sign, v
  | _ -> true, t

let as_bool_val t =
  match Term.view t with
  | Term.E_const { c_view = C_true; _ } -> Some true
  | Term.E_const { c_view = C_false; _ } -> Some false
  | _ -> None
