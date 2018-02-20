
open Solver_types

(* TODO: normalization of {!term_cell} for use in signatures? *)

type 'a cell = 'a Solver_types.term_cell =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | If of 'a * 'a * 'a
  | Case of 'a * 'a ID.Map.t
  | Custom of {
      view : 'a term_view_custom;
      tc : term_view_tc;
    }

type 'a custom = 'a Solver_types.term_view_custom = ..

type tc = Solver_types.term_view_tc = {
  tc_t_pp : 'a. 'a Fmt.printer -> 'a term_view_custom Fmt.printer;
  tc_t_equal : 'a. 'a CCEqual.t -> 'a term_view_custom CCEqual.t;
  tc_t_hash : 'a. 'a Hash.t -> 'a term_view_custom Hash.t;
  tc_t_ty : 'a. ('a -> ty) -> 'a term_view_custom -> ty;
  tc_t_is_semantic : 'a. 'a term_view_custom -> bool;
  tc_t_solve : cc_node term_view_custom -> cc_node term_view_custom -> solve_result;
  tc_t_sub : 'a. 'a term_view_custom -> 'a Sequence.t;
  tc_t_abs : 'a. self:'a -> 'a custom -> 'a * bool;
  tc_t_relevant : 'a. 'a term_view_custom -> 'a Sequence.t;
  tc_t_subst :
    'a 'b. ('a -> 'b) -> 'a term_view_custom -> 'b term_view_custom option;
  tc_t_explain : 'a. 'a CCEqual.t -> 'a term_view_custom -> 'a term_view_custom -> ('a * 'a) list;
}

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
    | Bool b -> Hash.bool b
    | App_cst (f,l) ->
      Hash.combine3 4 (Cst.hash f) (Hash.iarray sub_hash l)
    | If (a,b,c) -> Hash.combine4 7 (sub_hash a) (sub_hash b) (sub_hash c)
    | Case (u,m) ->
      let hash_m =
        Hash.seq (Hash.pair ID.hash sub_hash) (ID.Map.to_seq m)
      in
      Hash.combine3 8 (sub_hash u) hash_m
    | Custom {view;tc} -> tc.tc_t_hash sub_hash view

  (* equality that relies on physical equality of subterms *)
  let equal (a:A.t term_cell) b : bool = match a, b with
    | Bool b1, Bool b2 -> CCBool.equal b1 b2
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
    | Custom r1, Custom r2 ->
      r1.tc.tc_t_equal sub_eq r1.view r2.view
    | Bool _, _
    | App_cst _, _
    | If _, _
    | Case _, _
    | Custom _, _
      -> false
end[@@inline]

include Make_eq(struct
    type t = term
    let equal (t1:t) t2 = t1==t2
    let hash (t:term): int = t.term_id
  end)

let true_ = Bool true
let false_ = Bool false

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
  | Bool _ -> Ty.prop
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
  | Custom {view;tc} -> tc.tc_t_ty (fun t -> t.term_ty) view

module Tbl = CCHashtbl.Make(struct
    type t = term term_cell
    let equal = equal
    let hash = hash
  end)

