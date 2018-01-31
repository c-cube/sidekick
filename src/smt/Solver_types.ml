
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
  | Custom of {
      view: 'a term_view_custom;
      tc: term_view_tc;
    }

and 'a builtin =
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a list
  | B_or of 'a list
  | B_imply of 'a list * 'a

(** Methods on the custom term view whose leaves are ['a].
    Terms must be comparable, hashable, printable, and provide
    some additional theory handles.

    - [tc_t_sub] must return all immediate subterms (all ['a] contained in the term)

    - [tc_t_subst] must use the function to replace all subterms (all the ['a]
      returned by [tc_t_sub]) by ['b]

    - [tc_t_relevant] must return a subset of [tc_t_sub] (possibly the same set).
      The terms it returns will be activated and evaluated whenever possible.
      Terms in [tc_t_sub t \ tc_t_relevant t] are considered for
      congruence but not for evaluation.

    - If [t1] and [t2] satisfy [tc_t_is_semantic] and have the same type,
      then [tc_t_solve t1 t2] must succeed by returning some {!solve_result}.

    - if [tc_t_equal eq a b = true], then [tc_t_explain eq a b] must
      return all the pairs of equal subterms that are sufficient
      for [a] and [b] to be equal.
*)
and term_view_tc = {
  tc_t_pp : 'a. 'a Fmt.printer -> 'a term_view_custom Fmt.printer;
  tc_t_equal : 'a. 'a CCEqual.t -> 'a term_view_custom CCEqual.t;
  tc_t_hash : 'a. 'a Hash.t -> 'a term_view_custom Hash.t;
  tc_t_ty : 'a. ('a -> ty) -> 'a term_view_custom -> ty;
  tc_t_is_semantic : cc_node term_view_custom -> bool; (* is this a semantic term? semantic terms must be solvable *)
  tc_t_solve: cc_node term_view_custom -> cc_node term_view_custom -> solve_result; (* solve an equation between classes *)
  tc_t_sub : 'a. 'a term_view_custom -> 'a Sequence.t; (* iter on immediate subterms *)
  tc_t_relevant : 'a. 'a term_view_custom -> 'a Sequence.t; (* iter on relevant immediate subterms *)
  tc_t_subst : 'a 'b. ('a -> 'b) -> 'a term_view_custom -> 'b term_view_custom; (* substitute immediate subterms and canonize *)
  tc_t_explain : 'a. 'a CCEqual.t -> 'a term_view_custom -> 'a term_view_custom -> ('a * 'a) list;
  (* explain why the two views are equal *)
}

(** Custom term view for theories *)
and 'a term_view_custom = ..

(** The result of a call to {!solve}. *)
and solve_result =
  | Solve_ok of {
    subst: (cc_node * term) list; (** binding leaves to other terms *)
  } (** Success,  the two terms being equal is equivalent
        to the given substitution *)
  | Solve_fail of {
    expl: explanation;
  } (** Failure, because of the given explanation.
        The two terms cannot be equal *)

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
  mutable n_expl: explanation_forest_link; (* the rooted forest for explanations *)
  mutable n_payload: cc_node_payload list; (* list of theory payloads *)
}

(** Theory-extensible payloads *)
and cc_node_payload = ..

and explanation_forest_link =
  | E_none
  | E_some of {
      next: cc_node;
      expl: explanation;
    }

(* atomic explanation in the congruence closure *)
and explanation =
  | E_reduction (* by pure reduction, tautologically equal *)
  | E_lit of lit (* because of this literal *)
  | E_congruence of cc_node * cc_node (* these terms are congruent *)
  | E_injectivity of cc_node * cc_node (* injective function *)
  | E_reduce_eq of cc_node * cc_node (* reduce because those are equal by reduction *)
  | E_custom of {
      name: ID.t; (* name of the rule *)
      args: explanation list; (* sub-explanations *)
      pp: (ID.t * explanation list) Fmt.printer;
    } (** Custom explanation, typically for theories *)

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
  | Cst_recursive (* TODO: the set of Horn rules compiled from the def *)
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

let rec cmp_exp a b =
  let toint = function
    | E_congruence _ -> 0 | E_lit _ -> 1
    | E_reduction -> 2 | E_injectivity _ -> 3
    | E_reduce_eq _ -> 5
    | E_custom _ -> 6
  in
  begin match a, b with
    | E_congruence (t1,t2), E_congruence (u1,u2) ->
      CCOrd.(cmp_cc_node t1 u1 <?> (cmp_cc_node, t2, u2))
    | E_reduction, E_reduction -> 0
    | E_lit l1, E_lit l2 -> cmp_lit l1 l2
    | E_injectivity (t1,t2), E_injectivity (u1,u2) ->
      CCOrd.(cmp_cc_node t1 u1 <?> (cmp_cc_node, t2, u2))
    | E_reduce_eq (t1, u1), E_reduce_eq (t2,u2) ->
      CCOrd.(cmp_cc_node t1 t2 <?> (cmp_cc_node, u1, u2))
    | E_custom r1, E_custom r2 ->
      CCOrd.(ID.compare r1.name r2.name <?> (list cmp_exp, r1.args, r2.args))
    | E_congruence _, _ | E_lit _, _ | E_reduction, _
    | E_injectivity _, _ | E_reduce_eq _, _ | E_custom _, _
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
    | Builtin (B_and l) ->
      Fmt.fprintf out "(@[<hv1>and@ %a])" (Util.pp_list pp) l
    | Builtin (B_or l) ->
      Fmt.fprintf out "(@[<hv1>or@ %a@])" (Util.pp_list pp) l
    | Builtin (B_imply (a,b)) ->
      Fmt.fprintf out "(@[<hv1>=>@ %a@ %a@])" (Util.pp_list pp) a pp b
    | Builtin (B_eq (a,b)) ->
      Fmt.fprintf out "(@[<hv1>=@ %a@ %a@])" pp a pp b
    | Custom {view; tc} -> tc.tc_t_pp pp out view
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

let pp_explanation out (e:explanation) = match e with
  | E_reduction -> Fmt.string out "reduction"
  | E_lit lit -> pp_lit out lit
  | E_congruence (a,b) ->
    Format.fprintf out "(@[<hv1>congruence@ %a@ %a@])" pp_cc_node a pp_cc_node b
  | E_injectivity (a,b) ->
    Format.fprintf out "(@[<hv1>injectivity@ %a@ %a@])" pp_cc_node a pp_cc_node b
  | E_reduce_eq (t, u) ->
    Format.fprintf out "(@[<hv1>reduce_eq@ %a@ %a@])" pp_cc_node t pp_cc_node u
  | E_custom {name; args; pp} -> pp out (name,args)
