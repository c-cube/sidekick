
open Solver_types

(* TODO: normalization of {!term_cell} for use in signatures? *)

type t = term term_cell

module type ARG = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module Make_eq(A : ARG) = struct
  let sub_hash = A.hash
  let sub_eq = A.equal

  let hash (t:A.t term_cell) : int = match t with
    | True -> 1
    | App_cst (f,l) ->
      Hash.combine3 4 (Cst.hash f) (Hash.iarray sub_hash l)
    | If (a,b,c) -> Hash.combine4 7 (sub_hash a) (sub_hash b) (sub_hash c)
    | Case (u,m) ->
      let hash_m =
        Hash.seq (Hash.pair ID.hash sub_hash) (ID.Map.to_seq m)
      in
      Hash.combine3 8 (sub_hash u) hash_m
    | Builtin (B_not a) -> Hash.combine2 20 (sub_hash a)
    | Builtin (B_and l) -> Hash.combine2 21 (Hash.list sub_hash l)
    | Builtin (B_or l) -> Hash.combine2 22 (Hash.list sub_hash l)
    | Builtin (B_imply (l1,t2)) -> Hash.combine3 23 (Hash.list sub_hash l1) (sub_hash t2)
    | Builtin (B_eq (t1,t2)) -> Hash.combine3 24 (sub_hash t1) (sub_hash t2)
    | Builtin (B_distinct l) -> Hash.combine2 26 (Hash.list sub_hash l)
    | Custom {view;tc} -> tc.tc_t_hash sub_hash view

  (* equality that relies on physical equality of subterms *)
  let equal (a:A.t term_cell) b : bool = match a, b with
    | True, True -> true
    | App_cst (f1, a1), App_cst (f2, a2) ->
      Cst.equal f1 f2 && IArray.equal sub_eq a1 a2
    | If (a1,b1,c1), If (a2,b2,c2) ->
      sub_eq a1 a2 && sub_eq b1 b2 && sub_eq c1 c2
    | Case (u1, m1), Case (u2, m2) ->
      sub_eq u1 u2 &&
      ID.Map.for_all
        (fun k1 rhs1 ->
           try sub_eq rhs1 (ID.Map.find k1 m2)
           with Not_found -> false)
        m1
      &&
      ID.Map.for_all (fun k2 _ -> ID.Map.mem k2 m1) m2
    | Builtin b1, Builtin b2 ->
      begin match b1, b2 with
        | B_not a1, B_not a2 -> sub_eq a1 a2
        | B_and l1, B_and l2
        | B_or l1, B_or l2 -> CCEqual.list sub_eq l1 l2
        | B_distinct l1, B_distinct l2 -> CCEqual.list sub_eq l1 l2
        | B_eq (a1,b1), B_eq (a2,b2) -> sub_eq a1 a2 && sub_eq b1 b2
        | B_imply (a1,b1), B_imply (a2,b2) -> CCEqual.list sub_eq a1 a2 && sub_eq b1 b2
        | B_not _, _ | B_and _, _ | B_eq _, _
        | B_or _, _ | B_imply _, _ | B_distinct _, _
          -> false
      end
    | Custom r1, Custom r2 ->
      r1.tc.tc_t_equal sub_eq r1.view r2.view
    | True, _
    | App_cst _, _
    | If _, _
    | Case _, _
    | Builtin _, _
    | Custom _, _
      -> false
end[@@inline]

include Make_eq(struct
    type t = term
    let equal (t1:t) t2 = t1==t2
    let hash (t:term): int = t.term_id
  end)

let true_ = True

let app_cst f a = App_cst (f, a)
let const c = App_cst (c, IArray.empty)

let case u m = Case (u,m)
let if_ a b c =
  assert (Ty.equal b.term_ty c.term_ty);
  If (a,b,c)

let cstor_test cstor t =
  app_cst (Lazy.force cstor.cstor_test) (IArray.singleton t)

let cstor_proj cstor i t =
  let p = IArray.get (Lazy.force cstor.cstor_proj) i in
  app_cst p (IArray.singleton t)

let builtin b =
  let mk_ x = Builtin x in
  (* normalize a bit *)
  begin match b with
    | B_imply ([], x) -> x.term_cell
    | B_eq (a,b) when a.term_id = b.term_id -> true_
    | B_eq (a,b) when a.term_id > b.term_id -> mk_ @@ B_eq (b,a)
    | _ -> mk_ b
  end

let not_ t = match t.term_cell with
  | Builtin (B_not t') -> t'.term_cell
  | _ -> builtin (B_not t)

let and_ l = builtin (B_and l)
let or_ l = builtin (B_or l)
let imply a b = builtin (B_imply (a,b))
let eq a b = builtin (B_eq (a,b))
let distinct = function
  | [] | [_] -> true_
  | l -> builtin (B_distinct l)
let neq a b = distinct [a;b]

let custom ~tc view = Custom {view;tc}

(* type of an application *)
let rec app_ty_ ty l : Ty.t = match Ty.view ty, l with
  | _, [] -> ty
  | Arrow (ty_a,ty_rest), a::tail ->
    assert (Ty.equal ty_a a.term_ty);
    app_ty_ ty_rest tail
  | (Prop | Atomic _), _::_ ->
    assert false

let ty (t:t): Ty.t = match t with
  | True -> Ty.prop
  | App_cst (f, a) ->
    let n_args, ret = Cst.ty f |> Ty.unfold_n in
    if n_args = IArray.length a
    then ret (* fully applied *)
    else (
      assert (IArray.length a < n_args);
      app_ty_ (Cst.ty f) (IArray.to_list a)
    )
  | If (_,b,_) -> b.term_ty
  | Case (_,m) ->
    let _, rhs = ID.Map.choose m in
    rhs.term_ty
  | Builtin _ -> Ty.prop
  | Custom {view;tc} -> tc.tc_t_ty (fun t -> t.term_ty) view

module Tbl = CCHashtbl.Make(struct
    type t = term term_cell
    let equal = equal
    let hash = hash
  end)

