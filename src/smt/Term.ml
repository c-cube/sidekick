
open Solver_types

type t = term

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
    false_ = lazy (make st (Term_cell.not_ (true_ st)));
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

let not_ st t = make st (Term_cell.not_ t)

let and_l st = function
  | [] -> true_ st
  | [t] -> t
  | l -> make st (Term_cell.and_ l)

let or_l st = function
  | [] -> false_ st
  | [t] -> t
  | l -> make st (Term_cell.or_ l)

let and_ st a b = and_l st [a;b]
let or_ st a b = and_l st [a;b]
let imply st a b = match a with [] -> b | _ -> make st (Term_cell.imply a b)
let eq st a b = make st (Term_cell.eq a b)
let neq st a b = not_ st (eq st a b)
let builtin st b = make st (Term_cell.builtin b)

(* "eager" and, evaluating [a] first *)
let and_eager st a b = if_ st a b (false_ st)

let cstor_test st cstor t = make st (Term_cell.cstor_test cstor t)
let cstor_proj st cstor i t = make st (Term_cell.cstor_proj cstor i t)

(* might need to tranfer the negation from [t] to [sign] *)
let abs t : t * bool = match t.term_cell with
  | Builtin (B_not t) -> t, false
  | _ -> t, true

let fold_map_builtin
    (f:'a -> term -> 'a * term) (acc:'a) (b:t builtin): 'a * t builtin =
  let fold_binary acc a b =
    let acc, a = f acc a in
    let acc, b = f acc b in
    acc, a, b
  in
  match b with
    | B_not t ->
      let acc, t' = f acc t in
      acc, B_not t'
    | B_and l ->
      let acc, l = CCList.fold_map f acc l in
      acc, B_and l
    | B_or l ->
      let acc, l = CCList.fold_map f acc l in
      acc, B_or l
    | B_eq (a,b) ->
      let acc, a, b = fold_binary acc a b in
      acc, B_eq (a, b)
    | B_imply (a,b) ->
      let acc, a = CCList.fold_map f acc a in
      let acc, b = f acc b in
      acc, B_imply (a, b)

let is_const t = match t.term_cell with
  | App_cst (_, a) -> IArray.is_empty a
  | _ -> false

let map_builtin f b =
  let (), b = fold_map_builtin (fun () t -> (), f t) () b in
  b

let builtin_to_seq b yield = match b with
  | B_not t -> yield t
  | B_or l | B_and l -> List.iter yield l
  | B_imply (a,b) -> List.iter yield a; yield b
  | B_eq (a,b) -> yield a; yield b

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
      | True -> ()
      | App_cst (_,a) -> IArray.iter aux a
      | If (a,b,c) -> aux a; aux b; aux c
      | Case (t, m) ->
        aux t;
        ID.Map.iter (fun _ rhs -> aux rhs) m
      | Builtin b -> builtin_to_seq b aux
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
  term_cell=True;
}
