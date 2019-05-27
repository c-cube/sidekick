
open Base_types

type view = cst_view
type t = cst

let[@inline] id t = t.cst_id
let[@inline] view t = t.cst_view
let[@inline] make cst_id cst_view = {cst_id; cst_view}

let as_undefined (c:t) = match view c with
  | Cst_undef ty -> Some (c,ty)
  | Cst_def _ -> None

let[@inline] is_undefined c = match view c with Cst_undef _ -> true | _ -> false

let as_undefined_exn (c:t) = match as_undefined c with
  | Some tup -> tup
  | None -> assert false

let[@inline] mk_undef id ty = make id (Cst_undef ty)
let[@inline] mk_undef_const id ty = mk_undef id (Ty.Fun.mk [] ty)

let[@inline] do_cc (c:t) : bool = match view c with
| Cst_undef _ -> true
| Cst_def {do_cc;_} -> do_cc

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
