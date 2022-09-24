open Types_
open Term

type const_view += C_bool | C_eq | C_ite | C_not | C_true | C_false

let to_string = function
  | C_bool -> "Bool"
  | C_eq -> "="
  | C_ite -> "ite"
  | C_not -> "not"
  | C_true -> "true"
  | C_false -> "false"
  | _ -> assert false

let of_string = function
  | "Bool" -> Some C_bool
  | "=" -> Some C_eq
  | "ite" -> Some C_ite
  | "not" -> Some C_not
  | "true" -> Some C_true
  | "false" -> Some C_false
  | _ -> None

let ops : const_ops =
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
  in

  let hash = function
    | C_bool -> CCHash.int 167
    | C_eq -> CCHash.int 168
    | C_ite -> CCHash.int 169
    | C_not -> CCHash.int 170
    | C_true -> CCHash.int 171
    | C_false -> CCHash.int 172
    | _ -> assert false
  in

  let pp out self = Fmt.string out (to_string self) in
  let ser _sink self = "builtin", Ser_value.(string (to_string self)) in
  { Const.Ops.equal; hash; pp; ser }

(* TODO
   let deser _tst =
     Ser_decode.(
       let* v = string in
       match of_string v with
       | Some c -> return c
       | None -> fail "expected builtin")
*)

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
  const store @@ Const.make C_ite ops ~ty

let c_not store =
  let b = bool store in
  let ty = arrow store b b in
  const store @@ Const.make C_not ops ~ty

let eq store a b =
  if equal a b then
    true_ store
  else (
    let a, b =
      if compare a b <= 0 then
        a, b
      else
        b, a
    in
    app_l store (c_eq store) [ ty a; a; b ]
  )

let ite store a b c = app_l store (c_ite store) [ ty b; a; b; c ]

let not store a =
  (* turn [not (not u)] into [u] *)
  match view a with
  | E_app ({ view = E_const { c_view = C_not; _ }; _ }, u) -> u
  | E_const { c_view = C_true; _ } -> false_ store
  | E_const { c_view = C_false; _ } -> true_ store
  | _ -> app store (c_not store) a

let is_bool t =
  match view t with
  | E_const { c_view = C_bool; _ } -> true
  | _ -> false

let is_eq t =
  match view t with
  | E_const { c_view = C_eq; _ } -> true
  | _ -> false

let rec abs tst t =
  match view t with
  | E_app ({ view = E_const { c_view = C_not; _ }; _ }, u) ->
    let sign, v = abs tst u in
    Stdlib.not sign, v
  | E_const { c_view = C_false; _ } -> false, true_ tst
  | _ -> true, t

let as_bool_val t =
  match Term.view t with
  | Term.E_const { c_view = C_true; _ } -> Some true
  | Term.E_const { c_view = C_false; _ } -> Some false
  | _ -> None

let[@inline] open_eq t =
  let f, args = unfold_app t in
  match view f, args with
  | E_const { c_view = C_eq; _ }, [ _ty; a; b ] -> Some (a, b)
  | _ -> None
