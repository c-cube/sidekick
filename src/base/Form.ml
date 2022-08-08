open Types_
open Sidekick_core
module T = Term

type ty = Term.t
type term = Term.t

type ('a, 'args) view = ('a, 'args) Sidekick_core.Bool_view.t =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'args
  | B_or of 'args
  | B_imply of 'args * 'a
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
  if ID.equal fid id_and then
    B_and args
  else if ID.equal fid id_or then
    B_or args
  else if ID.equal fid id_imply then (
    match args with
    | [ arg; concl ] -> B_imply ([ arg ], concl)
    | _ -> raise_notrace Not_a_th_term
  ) else
    raise_notrace Not_a_th_term

let view (t : T.t) : (T.t, _) view =
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

(* TODO
   let and_l st l =
     match flatten_id id_and true l with
     | [] -> T.true_ st
     | l when List.exists T.is_false l -> T.false_ st
     | [ x ] -> x
     | args -> T.app_fun st Funs.and_ (CCArray.of_list args)

   let or_l st l =
     match flatten_id id_or false l with
     | [] -> T.false_ st
     | l when List.exists T.is_true l -> T.true_ st
     | [ x ] -> x
     | args -> T.app_fun st Funs.or_ (CCArray.of_list args)
*)

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
  | B_and l -> and_l tst l
  | B_or l -> or_l tst l
  | B_imply (a, b) -> imply_l tst a b
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

(*

module T = Base_types.Term
module Ty = Base_types.Ty
module Fun = Base_types.Fun
module Value = Base_types.Value
open Sidekick_th_bool_static

exception Not_a_th_term

let id_and = ID.make "and"
let id_or = ID.make "or"
let id_imply = ID.make "=>"

let view_id fid args =
  if ID.equal fid id_and then
    B_and (CCArray.to_iter args)
  else if ID.equal fid id_or then
    B_or (CCArray.to_iter args)
  else if ID.equal fid id_imply && CCArray.length args >= 2 then (
    (* conclusion is stored last *)
    let len = CCArray.length args in
    B_imply
      (Iter.of_array args |> Iter.take (len - 1), CCArray.get args (len - 1))
  ) else
    raise_notrace Not_a_th_term

let view_as_bool (t : T.t) : (T.t, _) bool_view =
  match T.view t with
  | Bool b -> B_bool b
  | Not u -> B_not u
  | Eq (a, b) when Ty.is_bool (T.ty a) -> B_equiv (a, b)
  | Ite (a, b, c) -> B_ite (a, b, c)
  | App_fun ({ fun_id; _ }, args) ->
    (try view_id fun_id args with Not_a_th_term -> B_atom t)
  | _ -> B_atom t

module Funs = struct
  let get_ty _ _ = Ty.bool ()

  let abs ~self _a =
    match T.view self with
    | Not u -> u, false
    | _ -> self, true

  (* no congruence closure for boolean terms *)
  let relevant _id _ _ = false

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

  let mk_fun ?(do_cc = false) id : Fun.t =
    {
      fun_id = id;
      fun_view =
        Fun_def { pp = None; abs; ty = get_ty; relevant; do_cc; eval = eval id };
    }

  let and_ = mk_fun id_and
  let or_ = mk_fun id_or
  let imply = mk_fun id_imply
  let ite = T.ite
end

let as_id id (t : T.t) : T.t array option =
  match T.view t with
  | App_fun ({ fun_id; _ }, args) when ID.equal id fun_id -> Some args
  | _ -> None

(* flatten terms of the given ID *)
let flatten_id op sign (l : T.t list) : T.t list =
  CCList.flat_map
    (fun t ->
      match as_id op t with
      | Some args -> CCArray.to_list args
      | None when (sign && T.is_true t) || ((not sign) && T.is_false t) ->
        [] (* idempotent *)
      | None -> [ t ])
    l

let and_l st l =
  match flatten_id id_and true l with
  | [] -> T.true_ st
  | l when List.exists T.is_false l -> T.false_ st
  | [ x ] -> x
  | args -> T.app_fun st Funs.and_ (CCArray.of_list args)

let or_l st l =
  match flatten_id id_or false l with
  | [] -> T.false_ st
  | l when List.exists T.is_true l -> T.true_ st
  | [ x ] -> x
  | args -> T.app_fun st Funs.or_ (CCArray.of_list args)

let and_ st a b = and_l st [ a; b ]
let or_ st a b = or_l st [ a; b ]
let and_a st a = and_l st (CCArray.to_list a)
let or_a st a = or_l st (CCArray.to_list a)
let eq = T.eq
let not_ = T.not_

let ite st a b c =
  match T.view a with
  | T.Bool ba ->
    if ba then
      b
    else
      c
  | _ -> T.ite st a b c

let equiv st a b =
  if T.equal a b then
    T.true_ st
  else if T.is_true a then
    b
  else if T.is_true b then
    a
  else if T.is_false a then
    not_ st b
  else if T.is_false b then
    not_ st a
  else
    T.eq st a b

let neq st a b = not_ st @@ eq st a b

let imply_a st xs y =
  if Array.length xs = 0 then
    y
  else
    T.app_fun st Funs.imply (CCArray.append xs [| y |])

let imply_l st xs y =
  match xs with
  | [] -> y
  | _ -> imply_a st (CCArray.of_list xs) y

let imply st a b = imply_a st [| a |] b
let xor st a b = not_ st (equiv st a b)

let distinct_l tst l =
  match l with
  | [] | [ _ ] -> T.true_ tst
  | l ->
    (* turn into [and_{i<j} t_i != t_j] *)
    let cs = CCList.diagonal l |> List.map (fun (a, b) -> neq tst a b) in
    and_l tst cs

let mk_bool st = function
  | B_bool b -> T.bool st b
  | B_atom t -> t
  | B_and l -> and_a st l
  | B_or l -> or_a st l
  | B_imply (a, b) -> imply_a st a b
  | B_ite (a, b, c) -> ite st a b c
  | B_equiv (a, b) -> equiv st a b
  | B_xor (a, b) -> not_ st (equiv st a b)
  | B_eq (a, b) -> T.eq st a b
  | B_neq (a, b) -> not_ st (T.eq st a b)
  | B_not t -> not_ st t
  | B_opaque_bool t -> t

module Gensym = struct
  type t = { tst: T.store; mutable fresh: int }

  let create tst : t = { tst; fresh = 0 }

  let fresh_term (self : t) ~pre (ty : Ty.t) : T.t =
    let name = Printf.sprintf "_tseitin_%s%d" pre self.fresh in
    self.fresh <- 1 + self.fresh;
    let id = ID.make name in
    T.const self.tst @@ Fun.mk_undef_const id ty
end

*)
