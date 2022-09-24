open Types_

type ty = Term.t
type t = Types_.uconst = { uc_id: ID.t; uc_ty: ty }

let[@inline] id self = self.uc_id
let[@inline] ty self = self.uc_ty
let equal a b = ID.equal a.uc_id b.uc_id
let compare a b = ID.compare a.uc_id b.uc_id
let hash a = ID.hash a.uc_id
let pp out c = ID.pp out c.uc_id

type Const.view += Uconst of t

let ops =
  let pp out = function
    | Uconst c -> pp out c
    | _ -> assert false
  in

  let equal a b =
    match a, b with
    | Uconst a, Uconst b -> equal a b
    | _ -> false
  in

  let hash = function
    | Uconst c -> Hash.combine2 522660 (hash c)
    | _ -> assert false
  in

  let ser ser_t = function
    | Uconst { uc_id; uc_ty } ->
      "uc", Ser_value.(list [ ID.ser uc_id; ser_t uc_ty ])
    | _ -> assert false
  in
  { Const.Ops.pp; equal; hash; ser }

let[@inline] make uc_id uc_ty : t = { uc_id; uc_ty }

let uconst tst (self : t) : Term.t =
  Term.const tst @@ Const.make (Uconst self) ops ~ty:self.uc_ty

let uconst_of_id tst id ty = uconst tst @@ make id ty

let uconst_of_id' tst id args ret =
  let ty = Term.arrow_l tst args ret in
  uconst_of_id tst id ty

let uconst_of_str tst name args ret : term =
  uconst_of_id' tst (ID.make name) args ret

module As_key = struct
  type nonrec t = t

  let compare = compare
  let equal = equal
  let hash = hash
end

module Map = CCMap.Make (As_key)
module Tbl = CCHashtbl.Make (As_key)
