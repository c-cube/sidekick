
open Solver_types

type t = term

type 'a custom = 'a Solver_types.term_view_custom = ..

type tc = Solver_types.term_view_tc = {
  tc_t_pp : 'a. 'a Fmt.printer -> 'a custom Fmt.printer;
  tc_t_equal : 'a. 'a CCEqual.t -> 'a custom CCEqual.t;
  tc_t_hash : 'a. 'a Hash.t -> 'a custom Hash.t;
  tc_t_ty : 'a. ('a -> ty) -> 'a custom -> ty;
  tc_t_is_semantic : 'a. 'a custom -> bool;
  tc_t_solve : cc_node custom -> cc_node custom -> solve_result;
  tc_t_sub : 'a. 'a custom -> 'a Sequence.t;
  tc_t_abs : 'a. self:'a -> 'a custom -> 'a * bool;
  tc_t_relevant : 'a. 'a custom -> 'a Sequence.t;
  tc_t_subst : 'a 'b. ('a -> 'b) -> 'a custom -> 'b custom;
  tc_t_explain : 'a. 'a CCEqual.t -> 'a custom -> 'a custom -> ('a * 'a) list;
}


let[@inline] id t = t.term_id
let[@inline] ty t = t.term_ty
let[@inline] cell t = t.term_cell

let equal = term_equal_
let hash = term_hash_
let compare a b = CCInt.compare a.term_id b.term_id

type state = {
  tbl : term Term_cell.Tbl.t;
  mutable n: int;
  true_ : t lazy_t;
  false_ : t lazy_t;
}

let mk_real_ st c : t =
  let term_ty = Term_cell.ty c in
  let t = {
    term_id= st.n;
    term_ty;
    term_cell=c;
  } in
  st.n <- 1 + st.n;
  Term_cell.Tbl.add st.tbl c t;
  t

let[@inline] make st (c:t term_cell) : t =
  try Term_cell.Tbl.find st.tbl c
  with Not_found -> mk_real_ st c

let[@inline] true_ st = Lazy.force st.true_
let[@inline] false_ st = Lazy.force st.false_

let create ?(size=1024) () : state =
  let rec st ={
    n=2;
    tbl=Term_cell.Tbl.create size;
    true_ = lazy (make st Term_cell.true_);
    false_ = lazy (make st Term_cell.false_);
  } in
  ignore (Lazy.force st.true_);
  ignore (Lazy.force st.false_); (* not true *)
  st

let[@inline] all_terms st = Term_cell.Tbl.values st.tbl

let app_cst st f a =
  let cell = Term_cell.app_cst f a in
  make st cell

let const st c = app_cst st c IArray.empty

let case st u m = make st (Term_cell.case u m)

let if_ st a b c = make st (Term_cell.if_ a b c)

(* "eager" and, evaluating [a] first *)
let and_eager st a b = if_ st a b (false_ st)

let custom st ~tc view = make st (Term_cell.custom ~tc view)

let cstor_test st cstor t = make st (Term_cell.cstor_test cstor t)
let cstor_proj st cstor i t = make st (Term_cell.cstor_proj cstor i t)

(* might need to tranfer the negation from [t] to [sign] *)
let abs t : t * bool = match t.term_cell with
  | Custom {view;tc} -> tc.tc_t_abs ~self:t view
  | _ -> t, true

let[@inline] is_true t = match t.term_cell with Bool true -> true | _ -> false
let[@inline]  is_false t = match t.term_cell with Bool false -> true | _ -> false

let[@inline] is_const t = match t.term_cell with
  | App_cst (_, a) -> IArray.is_empty a
  | _ -> false

let[@inline] is_custom t = match t.term_cell with
  | Custom _ -> true
  | _ -> false

let[@inline] is_semantic t = match t.term_cell with
  | Custom {view;tc} -> tc.tc_t_is_semantic view
  | _ -> false

module As_key = struct
    type t = term
    let compare = compare
    let equal = equal
    let hash = hash
end

module Map = CCMap.Make(As_key)
module Tbl = CCHashtbl.Make(As_key)

let to_seq t yield =
  let rec aux t =
    yield t;
    match t.term_cell with
      | Bool _ -> ()
      | App_cst (_,a) -> IArray.iter aux a
      | If (a,b,c) -> aux a; aux b; aux c
      | Case (t, m) ->
        aux t;
        ID.Map.iter (fun _ rhs -> aux rhs) m
      | Custom {view;tc} -> tc.tc_t_sub view aux
  in
  aux t

(* return [Some] iff the term is an undefined constant *)
let as_cst_undef (t:term): (cst * Ty.t) option =
  match t.term_cell with
    | App_cst (c, a) when IArray.is_empty a ->
      Cst.as_undefined c
    | _ -> None

(* return [Some (cstor,ty,args)] if the term is a constructor
   applied to some arguments *)
let as_cstor_app (t:term): (cst * data_cstor * term IArray.t) option =
  match t.term_cell with
    | App_cst ({cst_kind=Cst_cstor (lazy cstor); _} as c, a) ->
      Some (c,cstor,a)
    | _ -> None

(* typical view for unification/equality *)
type unif_form =
  | Unif_cst of cst * Ty.t
  | Unif_cstor of cst * data_cstor * term IArray.t
  | Unif_none

let as_unif (t:term): unif_form = match t.term_cell with
  | App_cst ({cst_kind=Cst_undef ty; _} as c, a) when IArray.is_empty a ->
    Unif_cst (c,ty)
  | App_cst ({cst_kind=Cst_cstor (lazy cstor); _} as c, a) ->
    Unif_cstor (c,cstor,a)
  | _ -> Unif_none

let pp = Solver_types.pp_term

let dummy : t = {
  term_id= -1;
  term_ty=Ty.prop;
  term_cell=Term_cell.true_;
}
