
open Solver_types

type t = term = {
  mutable term_id : int;
  mutable term_ty : ty;
  term_view : t term_view;
}

type 'a view = 'a term_view =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | Eq of 'a * 'a
  | If of 'a * 'a * 'a

let[@inline] id t = t.term_id
let[@inline] ty t = t.term_ty
let[@inline] view t = t.term_view

let equal = term_equal_
let hash = term_hash_
let compare a b = CCInt.compare a.term_id b.term_id

(* TODO: when GC is implemented, add a field for recycling IDs
   that have been free'd, so we can keep the ID space dense. *)

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
    term_view=c;
  } in
  st.n <- 1 + st.n;
  Term_cell.Tbl.add st.tbl c t;
  t

let[@inline] make st (c:t term_view) : t =
  try Term_cell.Tbl.find st.tbl c
  with Not_found -> mk_real_ st c

let[@inline] true_ st = Lazy.force st.true_
let[@inline] false_ st = Lazy.force st.false_
let bool st b = if b then true_ st else false_ st

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

let app_cst st f a =
  let cell = Term_cell.app_cst f a in
  make st cell

let[@inline] const st c = app_cst st c IArray.empty
let[@inline] if_ st a b c = make st (Term_cell.if_ a b c)
let[@inline] eq st a b = make st (Term_cell.eq a b)

(* "eager" and, evaluating [a] first *)
let and_eager st a b = if_ st a b (false_ st)

(* might need to tranfer the negation from [t] to [sign] *)
let abs t : t * bool = match view t with
  | App_cst ({cst_view=Cst_def def; _}, args) ->
    def.abs ~self:t args
  | _ -> t, true

let[@inline] is_true t = match view t with Bool true -> true | _ -> false
let[@inline] is_false t = match view t with Bool false -> true | _ -> false

let[@inline] is_const t = match view t with
  | App_cst (_, a) -> IArray.is_empty a
  | _ -> false

let cc_view (t:t) =
  let module C = Sidekick_cc in
  match view t with
  | Bool b -> C.Bool b
  | App_cst (f,_) when not (Cst.do_cc f) -> C.Opaque t (* skip *)
  | App_cst (f,args) -> C.App_fun (f, IArray.to_seq args)
  | Eq (a,b) -> C.Eq (a, b)
  | If (a,b,c) -> C.If (a,b,c)

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
    match view t with
    | Bool _ -> ()
    | App_cst (_,a) -> IArray.iter aux a
    | Eq (a,b) -> aux a; aux b
    | If (a,b,c) -> aux a; aux b; aux c
  in
  aux t

(* return [Some] iff the term is an undefined constant *)
let as_cst_undef (t:term): (cst * Ty.Fun.t) option =
  match view t with
  | App_cst (c, a) when IArray.is_empty a -> Cst.as_undefined c
  | _ -> None

let pp = Solver_types.pp_term


(* TODO 
  module T_arg = struct
    module Fun = Cst
    module Term = struct
      include Term
      let view = cc_view
    end
  end
  module Mini_cc = Mini_cc.Make(T_arg)
   *)
