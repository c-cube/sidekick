
open CDCL

module Fmt = CCFormat
module Node_bits = CCBitField.Make(struct end)

(* for objects that are expanded on demand only *)
type 'a lazily_expanded =
  | Lazy_some of 'a
  | Lazy_none

(* main term cell. *)
and term = {
  mutable term_id: int; (* unique ID *)
  mutable term_ty: ty;
  term_cell: term term_cell;
}

(* term shallow structure *)
and 'a term_cell =
  | True
  | App_cst of cst * 'a IArray.t (* full, first-order application *)
  | If of 'a * 'a * 'a
  | Case of 'a * 'a ID.Map.t (* check head constructor *)
  | Builtin of 'a builtin

and 'a builtin =
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a * 'a
  | B_or of 'a * 'a
  | B_imply of 'a * 'a

(** A node of the congruence closure.
    An equivalence class is represented by its "root" element,
    the representative.

    If there is a normal form in the congruence class, then the
    representative is a normal form *)
and cc_node = {
  n_term: term;
  mutable n_bits: Node_bits.t; (* bitfield for various properties *)
  mutable n_class: cc_node Bag.t; (* terms in the same equiv class *)
  mutable n_parents: cc_node Bag.t; (* parent terms of the whole equiv class *)
  mutable n_root: cc_node; (* representative of congruence class (itself if a representative) *)
  mutable n_expl: (cc_node * cc_explanation) option; (* the rooted forest for explanations *)
  mutable n_payload: cc_node_payload list; (* list of theory payloads *)
}

(** Theory-extensible payloads *)
and cc_node_payload = ..

(* atomic explanation in the congruence closure *)
and cc_explanation =
  | CC_reduction (* by pure reduction, tautologically equal *)
  | CC_lit of lit (* because of this literal *)
  | CC_congruence of cc_node * cc_node (* same shape *)
  | CC_injectivity of cc_node * cc_node (* arguments of those constructors *)
  | CC_reduce_eq of cc_node * cc_node (* reduce because those are equal *)
(* TODO: theory expl *)

(* boolean literal *)
and lit = {
  lit_view: lit_view;
  lit_sign: bool;
}

and lit_view =
  | Lit_fresh of ID.t (* fresh literals *)
  | Lit_atom of term
  | Lit_expanded of term (* expanded? used for recursive calls mostly *)
      (* TODO: remove this, unfold on the fly *)

and cst = {
  cst_id: ID.t;
  cst_kind: cst_kind;
}

and cst_kind =
  | Cst_undef of ty (* simple undefined constant *)
  | Cst_cstor of data_cstor lazy_t
  | Cst_proj of ty * data_cstor lazy_t * int (* [cstor, argument position] *)
  | Cst_test of ty * data_cstor lazy_t (* test if [cstor] *)
  | Cst_defined of ty * term lazy_t * cst_defined_info

(* what kind of constant is that? *)
and cst_defined_info =
  | Cst_recursive
  | Cst_non_recursive

(* this is a disjunction of sufficient conditions for the existence of
   some meta (cst). Each condition is a literal *)
and cst_exist_conds = lit lazy_t list ref

and 'a db_env = {
  db_st: 'a option list;
  db_size: int;
}

(* Hashconsed type *)
and ty = {
  mutable ty_id: int;
  ty_cell: ty_cell;
  ty_card: ty_card lazy_t;
}

and ty_card =
  | Finite
  | Infinite

and ty_def =
  | Uninterpreted
  | Data of datatype (* set of constructors *)

and datatype = {
  data_cstors: data_cstor ID.Map.t lazy_t;
}

(* TODO: in cstor, add:
   - for each selector, a special "magic" term for undefined, in
     case the selector is ill-applied (Collapse 2)  *)

(* a constructor *)
and data_cstor = {
  cstor_ty: ty;
  cstor_args: ty IArray.t; (* argument types *)
  cstor_proj: cst IArray.t lazy_t; (* projectors *)
  cstor_test: cst lazy_t; (* tester *)
  cstor_cst: cst; (* the cstor itself *)
  cstor_card: ty_card; (* cardinality of the constructor('s args) *)
}

and ty_cell =
  | Prop
  | Atomic of ID.t * ty_def
  | Arrow of ty * ty


let[@inline] term_equal_ (a:term) b = a==b
let[@inline] term_hash_ a = a.term_id
let[@inline] term_cmp_ a b = CCInt.compare a.term_id b.term_id

let cmp_lit a b =
  let c = CCBool.compare a.lit_sign b.lit_sign in
  if c<>0 then c
  else (
    let int_of_cell_ = function
      | Lit_fresh _ -> 0
      | Lit_atom _ -> 1
      | Lit_expanded _ -> 2
    in
    match a.lit_view, b.lit_view with
      | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
      | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
      | Lit_expanded t1, Lit_expanded t2 -> term_cmp_ t1 t2
      | Lit_fresh _, _
      | Lit_atom _, _
      | Lit_expanded _, _
        -> CCInt.compare (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)
  )

let cst_compare a b = ID.compare a.cst_id b.cst_id

let hash_lit a =
  let sign = a.lit_sign in
  match a.lit_view with
    | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
    | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
    | Lit_expanded t ->
      Hash.combine3 3 (Hash.bool sign) (term_hash_ t)

let cmp_cc_node a b = term_cmp_ a.n_term b.n_term

let cmp_cc_expl a b =
  let toint = function
    | CC_congruence _ -> 0 | CC_lit _ -> 1
    | CC_reduction -> 2 | CC_injectivity _ -> 3
    | CC_reduce_eq _ -> 5
  in
  begin match a, b with
    | CC_congruence (t1,t2), CC_congruence (u1,u2) ->
      CCOrd.(cmp_cc_node t1 u1 <?> (cmp_cc_node, t2, u2))
    | CC_reduction, CC_reduction -> 0
    | CC_lit l1, CC_lit l2 -> cmp_lit l1 l2
    | CC_injectivity (t1,t2), CC_injectivity (u1,u2) ->
      CCOrd.(cmp_cc_node t1 u1 <?> (cmp_cc_node, t2, u2))
    | CC_reduce_eq (t1, u1), CC_reduce_eq (t2,u2) ->
      CCOrd.(cmp_cc_node t1 t2 <?> (cmp_cc_node, u1, u2))
    | CC_congruence _, _ | CC_lit _, _ | CC_reduction, _
    | CC_injectivity _, _ | CC_reduce_eq _, _
      -> CCInt.compare (toint a)(toint b)
  end

let pp_cst out a = ID.pp out a.cst_id
let id_of_cst a = a.cst_id

let pp_db out (i,_) = Format.fprintf out "%%%d" i

let ty_unfold ty : ty list * ty =
  let rec aux acc ty = match ty.ty_cell with
    | Arrow (a,b) -> aux (a::acc) b
    | _ -> List.rev acc, ty
  in
  aux [] ty

let rec pp_ty out t = match t.ty_cell with
  | Prop -> Fmt.string out "prop"
  | Atomic (id, _) -> ID.pp out id
  | Arrow _ ->
    let args, ret = ty_unfold t in
    Format.fprintf out "(@[->@ %a@ %a@])"
      (Util.pp_list pp_ty) args pp_ty ret

let pp_term_top ~ids out t =
  let rec pp out t =
    pp_rec out t;
    (* FIXME
    if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id;
       *)
    ()

  and pp_rec out t = match t.term_cell with
    | True -> Fmt.string out "true"
    | App_cst (c, a) when IArray.is_empty a ->
      pp_id out (id_of_cst c)
    | App_cst (f,l) ->
      Fmt.fprintf out "(@[<1>%a@ %a@])" pp_id (id_of_cst f) (Util.pp_iarray pp) l
    | If (a, b, c) ->
      Fmt.fprintf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
    | Case (t,m) ->
      let pp_bind out (id,rhs) =
        Fmt.fprintf out "(@[<1>case %a@ %a@])" pp_id id pp rhs
      in
      let print_map =
        Fmt.seq ~sep:(Fmt.return "@ ") pp_bind
      in
      Fmt.fprintf out "(@[match %a@ (@[<hv>%a@])@])"
        pp t print_map (ID.Map.to_seq m)
    | Builtin (B_not t) -> Fmt.fprintf out "(@[<hv1>not@ %a@])" pp t
    | Builtin (B_and (a,b)) ->
      Fmt.fprintf out "(@[<hv1>and@ %a@ %a@])" pp a pp b
    | Builtin (B_or (a,b)) ->
      Fmt.fprintf out "(@[<hv1>or@ %a@ %a@])" pp a pp b
    | Builtin (B_imply (a,b)) ->
      Fmt.fprintf out "(@[<hv1>=>@ %a@ %a@])" pp a pp b
    | Builtin (B_eq (a,b)) ->
      Fmt.fprintf out "(@[<hv1>=@ %a@ %a@])" pp a pp b
  and pp_id =
    if ids then ID.pp else ID.pp_name
  in
  pp out t

let pp_term = pp_term_top ~ids:false

let pp_lit out l =
  let pp_lit_view out = function
    | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
    | Lit_atom t -> pp_term out t
    | Lit_expanded t -> Format.fprintf out "(@[<1>expanded@ %a@])" pp_term t
  in
  if l.lit_sign then pp_lit_view out l.lit_view
  else Format.fprintf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

let pp_cc_node out n = pp_term out n.n_term

let pp_cc_explanation out (e:cc_explanation) = match e with
  | CC_reduction -> Fmt.string out "reduction"
  | CC_lit lit -> pp_lit out lit
  | CC_congruence (a,b) ->
    Format.fprintf out "(@[<hv1>congruence@ %a@ %a@])" pp_cc_node a pp_cc_node b
  | CC_injectivity (a,b) ->
    Format.fprintf out "(@[<hv1>injectivity@ %a@ %a@])" pp_cc_node a pp_cc_node b
  | CC_reduce_eq (t, u) ->
    Format.fprintf out "(@[<hv1>reduce_eq@ %a@ %a@])" pp_cc_node t pp_cc_node u
