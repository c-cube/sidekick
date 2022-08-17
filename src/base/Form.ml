open Types_
open Sidekick_core
module T = Term

type ty = Term.t
type term = Term.t

type 'a view = 'a Sidekick_core.Bool_view.t =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'a * 'a
  | B_or of 'a * 'a
  | B_imply of 'a * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_atom of 'a

(* ### allocate special IDs for connectors *)

let id_and = ID.make "and"
let id_or = ID.make "or"
let id_imply = ID.make "=>"

(* ### view *)

exception Not_a_th_term

let view_id_ fid args =
  match args with
  | [ a; b ] when ID.equal fid id_and -> B_and (a, b)
  | [ a; b ] when ID.equal fid id_or -> B_or (a, b)
  | [ a; b ] when ID.equal fid id_imply -> B_imply (a, b)
  | _ -> raise_notrace Not_a_th_term

let view (t : T.t) : T.t view =
  let hd, args = T.unfold_app t in
  match T.view hd, args with
  | E_const { Const.c_view = T.C_true; _ }, [] -> B_bool true
  | E_const { Const.c_view = T.C_false; _ }, [] -> B_bool false
  | E_const { Const.c_view = T.C_not; _ }, [ a ] -> B_not a
  | E_const { Const.c_view = T.C_eq; _ }, [ _ty; a; b ] -> B_eq (a, b)
  | E_const { Const.c_view = T.C_ite; _ }, [ _ty; a; b; c ] -> B_ite (a, b, c)
  | E_const { Const.c_view = Uconst.Uconst { uc_id; _ }; _ }, _ ->
    (try view_id_ uc_id args with Not_a_th_term -> B_atom t)
  | _ -> B_atom t

let c_and tst : Term.t =
  let bool = Term.bool tst in
  Uconst.uconst_of_id' tst id_and [ bool; bool ] bool

let c_or tst : Term.t =
  let bool = Term.bool tst in
  Uconst.uconst_of_id' tst id_or [ bool; bool ] bool

let c_imply tst : Term.t =
  let bool = Term.bool tst in
  Uconst.uconst_of_id' tst id_imply [ bool; bool ] bool

let bool = Term.bool_val
let and_ tst a b = Term.app_l tst (c_and tst) [ a; b ]
let or_ tst a b = Term.app_l tst (c_or tst) [ a; b ]
let imply tst a b = Term.app_l tst (c_imply tst) [ a; b ]
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

let and_l tst = function
  | [] -> T.true_ tst
  | [ x ] -> x
  | x :: tl -> List.fold_left (and_ tst) x tl

let or_l tst = function
  | [] -> T.false_ tst
  | [ x ] -> x
  | x :: tl -> List.fold_left (or_ tst) x tl

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
  | B_and (a, b) -> and_ tst a b
  | B_or (a, b) -> or_ tst a b
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
