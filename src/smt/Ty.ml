
open CDCL
open Solver_types

type t = ty
type cell = ty_cell
type def = ty_def

let view t = t.ty_cell

let equal a b = a.ty_id = b.ty_id
let compare a b = CCInt.compare a.ty_id b.ty_id
let hash a = a.ty_id

module Tbl_cell = CCHashtbl.Make(struct
    type t = ty_cell
    let equal a b = match a, b with
      | Prop, Prop -> true
      | Atomic (i1,_), Atomic (i2,_) -> ID.equal i1 i2
      | Arrow (a1,b1), Arrow (a2,b2) ->
        equal a1 a2 && equal b1 b2
      | Prop, _
      | Atomic _, _
      | Arrow _, _ -> false

    let hash t = match t with
      | Prop -> 1
      | Atomic (i,_) -> Hash.combine2 2 (ID.hash i)
      | Arrow (a,b) -> Hash.combine3 3 (hash a) (hash b)
  end)

(* build a type *)
let make_ : ty_cell -> card:ty_card lazy_t -> t =
  let tbl : t Tbl_cell.t = Tbl_cell.create 128 in
  let n = ref 0 in
  fun c ~card ->
    try Tbl_cell.find tbl c
    with Not_found ->
      let ty_id = !n in
      incr n;
      let ty = {ty_id; ty_cell=c; ty_card=card; } in
      Tbl_cell.add tbl c ty;
      ty

let prop = make_ Prop ~card:(Lazy.from_val Finite)

let atomic id def ~card = make_ (Atomic (id,def)) ~card

let arrow a b =
  let card = lazy (Ty_card.(Lazy.force b.ty_card ^ Lazy.force a.ty_card)) in
  make_ (Arrow (a,b)) ~card

let arrow_l = List.fold_right arrow

let is_prop t =
  match t.ty_cell with | Prop -> true | _ -> false

let is_data t =
  match t.ty_cell with | Atomic (_, Data _) -> true | _ -> false

let is_uninterpreted t =
  match t.ty_cell with | Atomic (_, Uninterpreted) -> true | _ -> false

let is_arrow t =
  match t.ty_cell with | Arrow _ -> true | _ -> false

let unfold = ty_unfold

let unfold_n ty : int * t =
  let rec aux n ty = match ty.ty_cell with
    | Arrow (_,b) -> aux (n+1) b
    | _ -> n, ty
  in
  aux 0 ty

let pp = pp_ty

(* representation as a single identifier *)
let rec mangle t : string = match t.ty_cell with
  | Prop -> "prop"
  | Atomic (id,_) -> ID.to_string id
  | Arrow (a,b) -> mangle a ^ "_" ^ mangle b

module Tbl = CCHashtbl.Make(struct
    type t = ty
    let equal = equal
    let hash = hash
  end)
