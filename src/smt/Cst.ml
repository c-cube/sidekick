
open CDCL
open Solver_types

type t = cst

let id t = t.cst_id

let ty_of_kind = function
  | Cst_defined (ty, _, _)
  | Cst_undef ty
  | Cst_test (ty, _)
  | Cst_proj (ty, _, _) -> ty
  | Cst_cstor (lazy cstor) -> cstor.cstor_ty

let ty t = ty_of_kind t.cst_kind

let arity t = fst (Ty.unfold_n (ty t))

let make cst_id cst_kind = {cst_id; cst_kind}
let make_cstor id ty cstor =
  let _, ret = Ty.unfold ty in
  assert (Ty.is_data ret);
  make id (Cst_cstor cstor)
let make_proj id ty cstor i =
  make id (Cst_proj (ty, cstor, i))
let make_tester id ty cstor =
  make id (Cst_test (ty, cstor))

let make_defined id ty t info = make id (Cst_defined (ty, t, info))

let make_undef id ty = make id (Cst_undef ty)

let as_undefined (c:t) = match c.cst_kind with
  | Cst_undef ty -> Some (c,ty)
  | Cst_defined _ | Cst_cstor _ | Cst_proj _ | Cst_test _
    -> None

let as_undefined_exn (c:t) = match as_undefined c with
  | Some tup -> tup
  | None -> assert false

let is_finite_cstor c = match c.cst_kind with
  | Cst_cstor (lazy {cstor_card=Finite; _}) -> true
  | _ -> false

let equal a b = ID.equal a.cst_id b.cst_id
let compare a b = ID.compare a.cst_id b.cst_id
let hash t = ID.hash t.cst_id
let pp out a = ID.pp out a.cst_id

module Map = CCMap.Make(struct
    type t = cst
    let compare = compare
  end)
module Tbl = CCHashtbl.Make(struct
    type t = cst
    let equal = equal
    let hash = hash
  end)
