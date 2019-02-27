
module ID = Sidekick_smt.ID
module T = Sidekick_smt.Term
module Ty = Sidekick_smt.Ty
open Sidekick_smt.Solver_types

open Bool_intf

type term = T.t
type t = T.t
type state = T.state

type 'a view = 'a Bool_intf.view

exception Not_a_th_term

let id_not = ID.make "not"
let id_and = ID.make "and"
let id_or = ID.make "or"
let id_imply = ID.make "=>"

let equal = T.equal
let hash = T.hash

let view_id cst_id args =
  if ID.equal cst_id id_not && IArray.length args=1 then (
    B_not (IArray.get args 0)
  ) else if ID.equal cst_id id_and then (
    B_and args
  ) else if ID.equal cst_id id_or then (
    B_or args
  ) else if ID.equal cst_id id_imply && IArray.length args >= 2 then (
    (* conclusion is stored first *)
    let len = IArray.length args in
    B_imply (IArray.sub args 1 (len-1), IArray.get args 0)
  ) else (
    raise_notrace Not_a_th_term
  )

let view_as_bool (t:T.t) : T.t view =
  match T.view t with
  | App_cst ({cst_id; _}, args) ->
    (try view_id cst_id args with Not_a_th_term -> B_atom t)
  | _ -> B_atom t

module C = struct

  let get_ty _ _ = Ty.prop

  let abs ~self _a =
    match T.view self with
    | App_cst ({cst_id;_}, args) when ID.equal cst_id id_not && IArray.length args=1 ->
      (* [not a] --> [a, false] *)
      IArray.get args 0, false
    | _ -> self, true

  let eval id args =
    let module Value = Sidekick_smt.Value in
    match view_id id args with
    | B_not (V_bool b) -> Value.bool (not b)
    | B_and a when IArray.for_all Value.is_true a -> Value.true_
    | B_and a when IArray.exists Value.is_false a -> Value.false_
    | B_or a when IArray.exists Value.is_true a -> Value.true_
    | B_or a when IArray.for_all Value.is_false a -> Value.false_
    | B_imply (_, V_bool true) -> Value.true_
    | B_imply (a,_) when IArray.exists Value.is_false a -> Value.true_
    | B_imply (a,b) when IArray.for_all Value.is_bool a && Value.is_bool b -> Value.false_
    | B_atom v -> v
    | B_not _ | B_and _ | B_or _ | B_imply _
        -> Error.errorf "non boolean value in boolean connective"

  (* no congruence closure for boolean terms *)
  let relevant _id _ _ = false

  let mk_cst ?(do_cc=false) id : cst =
    {cst_id=id;
     cst_view=Cst_def {
         pp=None; abs; ty=get_ty; relevant; do_cc; eval=eval id; }; }

  let not = mk_cst id_not
  let and_ = mk_cst id_and
  let or_ = mk_cst id_or
  let imply = mk_cst id_imply
end

let as_id id (t:T.t) : T.t IArray.t option =
  match T.view t with
  | App_cst ({cst_id; _}, args) when ID.equal id cst_id -> Some args
  | _ -> None

(* flatten terms of the given ID *)
let flatten_id op sign (l:T.t list) : T.t list =
  CCList.flat_map
    (fun t -> match as_id op t with
       | Some args -> IArray.to_list args
       | None when (sign && T.is_true t) || (not sign && T.is_false t) ->
         [] (* idempotent *)
       | None -> [t])
    l

let and_l st l =
  match flatten_id id_and true l with
  | [] -> T.true_ st
  | l when List.exists T.is_false l -> T.false_ st
  | [x] -> x
  | args -> T.app_cst st C.and_ (IArray.of_list args)

let or_l st l =
  match flatten_id id_or false l with
  | [] -> T.false_ st
  | l when List.exists T.is_true l -> T.true_ st
  | [x] -> x
  | args -> T.app_cst st C.or_ (IArray.of_list args)

let and_ st a b = and_l st [a;b]
let or_ st a b = or_l st [a;b]
let and_a st a = and_l st (IArray.to_list a)
let or_a st a = or_l st (IArray.to_list a)

let eq = T.eq

let not_ st a =
  match as_id id_not a, T.view a with
  | _, Bool false -> T.true_ st
  | _, Bool true -> T.false_ st
  | Some args, _ ->
    assert (IArray.length args = 1);
    IArray.get args 0
  | None, _ -> T.app_cst st C.not (IArray.singleton a)

let neq st a b = not_ st @@ eq st a b

let imply_a st xs y =
  if IArray.is_empty xs then y
  else T.app_cst st C.imply (IArray.append (IArray.singleton y) xs)

let imply_l st xs y = match xs with
  | [] -> y
  | _ -> T.app_cst st C.imply (IArray.of_list @@ y :: xs)

let imply st a b = imply_a st (IArray.singleton a) b

let make st = function
  | B_atom t -> t
  | B_and l -> and_a st l
  | B_or l -> or_a st l
  | B_imply (a,b) -> imply_a st a b
  | B_not t -> not_ st t
