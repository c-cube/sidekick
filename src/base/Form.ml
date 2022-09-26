open Sidekick_core
module T = Term

type term = Term.t

type 'a view = 'a Sidekick_core.Bool_view.t =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'a list
  | B_or of 'a list
  | B_imply of 'a * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_atom of 'a

type Const.view += C_and | C_or | C_imply

let ops =
  let pp out = function
    | C_and -> Fmt.string out "and"
    | C_or -> Fmt.string out "or"
    | C_imply -> Fmt.string out "=>"
    | _ -> assert false
  in

  let equal a b =
    match a, b with
    | C_and, C_and | C_or, C_or | C_imply, C_imply -> true
    | _ -> false
  in

  let hash = function
    | C_and -> Hash.int 425
    | C_or -> Hash.int 426
    | C_imply -> Hash.int 427
    | _ -> assert false
  in

  let ser _sink =
    Ser_value.(
      function
      | C_and -> "and", null
      | C_or -> "or", null
      | C_imply -> "=>", null
      | _ -> assert false)
  in
  { Const.Ops.pp; equal; hash; ser }

let const_decoders : Const.decoders =
  [
    ("and", ops, Ser_decode.(fun _ -> return C_and));
    ("or", ops, Ser_decode.(fun _ -> return C_or));
    ("=>", ops, Ser_decode.(fun _ -> return C_imply));
  ]

(* ### view *)

let view (t : T.t) : T.t view =
  let hd, args = T.unfold_app t in
  match T.view hd, args with
  | E_const { Const.c_view = T.C_true; _ }, [] -> B_bool true
  | E_const { Const.c_view = T.C_false; _ }, [] -> B_bool false
  | E_const { Const.c_view = T.C_not; _ }, [ a ] -> B_not a
  | E_const { Const.c_view = T.C_eq; _ }, [ _ty; a; b ] ->
    if Ty.is_bool (Term.ty a) then
      B_equiv (a, b)
    else
      B_eq (a, b)
  | E_const { Const.c_view = T.C_ite; _ }, [ _ty; a; b; c ] -> B_ite (a, b, c)
  | E_const { Const.c_view = C_imply; _ }, [ a; b ] -> B_imply (a, b)
  | E_app_fold { f; args; acc0 }, [] ->
    (match T.view f, T.view acc0 with
    | ( E_const { Const.c_view = C_and; _ },
        E_const { Const.c_view = T.C_true; _ } ) ->
      B_and args
    | ( E_const { Const.c_view = C_or; _ },
        E_const { Const.c_view = T.C_false; _ } ) ->
      B_or args
    | _ -> B_atom t)
  | _ -> B_atom t

let ty2b_ tst =
  let bool = Term.bool tst in
  Term.arrow_l tst [ bool; bool ] bool

let c_and tst : Const.t = Const.make C_and ops ~ty:(ty2b_ tst)
let c_or tst : Const.t = Const.make C_or ops ~ty:(ty2b_ tst)
let c_imply tst : Const.t = Const.make C_imply ops ~ty:(ty2b_ tst)

let and_l tst = function
  | [] -> T.true_ tst
  | [ x ] -> x
  | l ->
    Term.app_fold tst l ~f:(Term.const tst @@ c_and tst) ~acc0:(T.true_ tst)

let or_l tst = function
  | [] -> T.false_ tst
  | [ x ] -> x
  | l ->
    Term.app_fold tst l ~f:(Term.const tst @@ c_or tst) ~acc0:(T.false_ tst)

let bool = Term.bool_val
let and_ tst a b = and_l tst [ a; b ]
let or_ tst a b = or_l tst [ a; b ]
let imply tst a b : Term.t = T.app_l tst (T.const tst @@ c_imply tst) [ a; b ]
let eq = T.eq
let not_ = T.not
let ite = T.ite
let neq st a b = not_ st @@ eq st a b
let imply_l tst xs y = List.fold_right (imply tst) xs y

let equiv tst a b =
  if (not (T.is_bool (T.ty a))) || not (T.is_bool (T.ty b)) then
    failwith "Form.equiv: takes boolean arguments";
  T.eq tst a b

let xor tst a b = not_ tst (equiv tst a b)

let distinct_l tst l =
  match l with
  | [] | [ _ ] -> T.true_ tst
  | l ->
    (* turn into [and_{i<j} t_i != t_j] *)
    let cs = CCList.diagonal l |> List.map (fun (a, b) -> neq tst a b) in
    and_l tst cs

let mk_of_view tst = function
  | B_bool b -> T.bool_val tst b
  | B_atom t -> t
  | B_and l -> and_l tst l
  | B_or l -> or_l tst l
  | B_imply (a, b) -> imply tst a b
  | B_ite (a, b, c) -> ite tst a b c
  | B_equiv (a, b) -> equiv tst a b
  | B_xor (a, b) -> not_ tst (equiv tst a b)
  | B_eq (a, b) -> T.eq tst a b
  | B_neq (a, b) -> not_ tst (T.eq tst a b)
  | B_not t -> not_ tst t

(*
  let eval id args =
    let open Value in
    match view_id id args with
    | B_bool b -> Value.bool b
    | B_not (V_bool b) -> Value.bool (not b)
    | B_and a when Iter.for_all Value.is_true a -> Value.true_
    | B_and a when Iter.exists Value.is_false a -> Value.false_
    | B_or a when Iter.exists Value.is_true a -> Value.true_
    | B_or a when Iter.for_all Value.is_false a -> Value.false_
    | B_imply (_, V_bool true) -> Value.true_
    | B_imply (a, _) when Iter.exists Value.is_false a -> Value.true_
    | B_imply (a, b) when Iter.for_all Value.is_true a && Value.is_false b ->
      Value.false_
    | B_ite (a, b, c) ->
      if Value.is_true a then
        b
      else if Value.is_false a then
        c
      else
        Error.errorf "non boolean value %a in ite" Value.pp a
    | B_equiv (a, b) | B_eq (a, b) -> Value.bool (Value.equal a b)
    | B_xor (a, b) | B_neq (a, b) -> Value.bool (not (Value.equal a b))
    | B_atom v -> v
    | B_opaque_bool t -> Error.errorf "cannot evaluate opaque bool %a" pp t
    | B_not _ | B_and _ | B_or _ | B_imply _ ->
      Error.errorf "non boolean value in boolean connective"
      *)
