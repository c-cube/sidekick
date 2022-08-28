open Types_

type select = Types_.select = {
  select_id: ID.t;
  select_cstor: cstor;
  select_ty: ty lazy_t;
  select_i: int;
}

type cstor = Types_.cstor = {
  cstor_id: ID.t;
  cstor_is_a: ID.t;
  mutable cstor_arity: int;
  cstor_args: select list lazy_t;
  cstor_ty_as_data: data;
  cstor_ty: ty lazy_t;
}

type t = data = {
  data_id: ID.t;
  data_cstors: cstor ID.Map.t lazy_t;
  data_as_ty: ty lazy_t;
}

let pp out d = ID.pp out d.data_id
let equal a b = ID.equal a.data_id b.data_id
let hash a = ID.hash a.data_id

(** Datatype selectors.

    A selector is a kind of function that allows to obtain an argument
    of a given constructor. *)
module Select = struct
  type t = Types_.select = {
    select_id: ID.t;
    select_cstor: cstor;
    select_ty: ty lazy_t;
    select_i: int;
  }

  let ty sel = Lazy.force sel.select_ty

  let equal a b =
    ID.equal a.select_id b.select_id
    && ID.equal a.select_cstor.cstor_id b.select_cstor.cstor_id
    && a.select_i = b.select_i

  let hash a =
    Hash.combine4 1952 (ID.hash a.select_id)
      (ID.hash a.select_cstor.cstor_id)
      (Hash.int a.select_i)

  let pp out self =
    Fmt.fprintf out "select.%a[%d]" ID.pp self.select_cstor.cstor_id
      self.select_i
end

(** Datatype constructors.

    A datatype has one or more constructors, each of which is a special
    kind of function symbol. Constructors are injective and pairwise distinct. *)
module Cstor = struct
  type t = cstor

  let hash c = ID.hash c.cstor_id
  let ty_args c = Lazy.force c.cstor_args |> List.map Select.ty

  let select_idx c i =
    let (lazy sels) = c.cstor_args in
    if i >= List.length sels then invalid_arg "cstor.select_idx: out of bound";
    List.nth sels i

  let equal a b = ID.equal a.cstor_id b.cstor_id
  let pp out c = ID.pp out c.cstor_id
end

type Const.view +=
  | Data of data
  | Cstor of cstor
  | Select of select
  | Is_a of cstor

let ops =
  (module struct
    let pp out = function
      | Data d -> pp out d
      | Cstor c -> Cstor.pp out c
      | Select s -> Select.pp out s
      | Is_a c -> Fmt.fprintf out "(_ is %a)" Cstor.pp c
      | _ -> assert false

    let equal a b =
      match a, b with
      | Data a, Data b -> equal a b
      | Cstor a, Cstor b -> Cstor.equal a b
      | Select a, Select b -> Select.equal a b
      | Is_a a, Is_a b -> Cstor.equal a b
      | _ -> false

    let hash = function
      | Data d -> Hash.combine2 592 (hash d)
      | Cstor c -> Hash.combine2 593 (Cstor.hash c)
      | Select s -> Hash.combine2 594 (Select.hash s)
      | Is_a c -> Hash.combine2 595 (Cstor.hash c)
      | _ -> assert false
  end : Const.DYN_OPS)

let data tst d : Term.t =
  Term.const tst @@ Const.make (Data d) ops ~ty:(Term.type_ tst)

let cstor tst c : Term.t =
  let ty_ret = Lazy.force c.cstor_ty in
  let ty_args =
    List.map (fun s -> Lazy.force s.select_ty) (Lazy.force c.cstor_args)
  in
  let ty = Term.arrow_l tst ty_args ty_ret in
  Term.const tst @@ Const.make (Cstor c) ops ~ty

let select tst s : Term.t =
  let ty_ret = Lazy.force s.select_ty in
  let ty_arg = data tst s.select_cstor.cstor_ty_as_data in
  let ty = Term.arrow tst ty_arg ty_ret in
  Term.const tst @@ Const.make (Select s) ops ~ty

let is_a tst c : Term.t =
  let ty_arg = Lazy.force c.cstor_ty in
  let ty = Term.arrow tst ty_arg (Term.bool tst) in
  Term.const tst @@ Const.make (Is_a c) ops ~ty

let as_data t =
  match Term.view t with
  | E_const { Const.c_view = Data d; _ } -> Some d
  | _ -> None

let as_cstor t =
  match Term.view t with
  | E_const { Const.c_view = Cstor c; _ } -> Some c
  | _ -> None

let as_select t =
  match Term.view t with
  | E_const { Const.c_view = Select s; _ } -> Some s
  | _ -> None

let as_is_a t =
  match Term.view t with
  | E_const { Const.c_view = Is_a c; _ } -> Some c
  | _ -> None
