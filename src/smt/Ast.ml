
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Fmt = CCFormat
module S = CCSexp

type 'a or_error = ('a, string) CCResult.t

exception Error of string
exception Ill_typed of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("ast error: " ^ msg)
      | Ill_typed msg -> Some ("ill-typed: " ^ msg)
      | _ -> None)

let errorf msg =
  CCFormat.ksprintf ~f:(fun e -> raise (Error e)) msg

(** {2 Types} *)

module Var = struct
  type 'ty t = {
    id: ID.t;
    ty: 'ty;
  }

  let make id ty = {id;ty}
  let makef ~ty fmt =
    CCFormat.ksprintf fmt ~f:(fun s -> make (ID.make s) ty)
  let copy {id;ty} = {ty; id=ID.copy id}
  let id v = v.id
  let ty v = v.ty

  let equal a b = ID.equal a.id b.id
  let compare a b = ID.compare a.id b.id
  let pp out v = ID.pp out v.id
end

module Ty = struct
  type t =
    | Prop
    | Const of ID.t
    | Arrow of t * t

  let prop = Prop
  let const id = Const id
  let arrow a b = Arrow (a,b)
  let arrow_l = List.fold_right arrow

  let to_int_ = function
    | Prop -> 0
    | Const _ -> 1
    | Arrow _ -> 2

  let (<?>) = CCOrd.(<?>)

  let rec compare a b = match a, b with
    | Prop, Prop -> 0
    | Const a, Const b -> ID.compare a b
    | Arrow (a1,a2), Arrow (b1,b2) ->
      compare a1 b1 <?> (compare, a2,b2)
    | Prop, _
    | Const _, _
    | Arrow _, _ -> CCInt.compare (to_int_ a) (to_int_ b)

  let equal a b = compare a b = 0

  let hash _ = 0 (* TODO *)

  let unfold ty =
    let rec aux acc ty = match ty with
      | Arrow (a,b) -> aux (a::acc) b
      | _ -> List.rev acc, ty
    in
    aux [] ty

  let rec pp out = function
    | Prop -> Fmt.string out "prop"
    | Const id -> ID.pp out id
    | Arrow _ as ty ->
      let args, ret = unfold ty in
      Fmt.fprintf out "(@[-> %a@ %a@])"
        (Util.pp_list ~sep:" " pp) args pp ret

  (** {2 Datatypes} *)

  type data = {
    data_id: ID.t;
    data_cstors: t ID.Map.t;
  }

  (* FIXME
  let data_to_sexp d =
    let cstors =
      ID.Map.fold
        (fun c ty acc ->
           let ty_args, _ = unfold ty in
           let c_sexp = match ty_args with
             | [] -> ID.to_sexp c
             | _::_ -> S.of_list (ID.to_sexp c :: List.map to_sexp ty_args)
           in
           c_sexp :: acc)
        d.data_cstors []
    in
    S.of_list (ID.to_sexp d.data_id :: cstors)
     *)

  module Map = CCMap.Make(struct
      type _t = t
      type t = _t
      let compare = compare
    end)

  let ill_typed fmt =
    CCFormat.ksprintf
      ~f:(fun s -> raise (Ill_typed s))
      fmt
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply
  | Eq

type binder =
  | Fun
  | Forall
  | Exists
  | Mu

type term = {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | Unknown of var (* meta var *)
  | App of term * term list
  | If of term * term * term
  | Select of select * term
  | Match of term * (var list * term) ID.Map.t
  | Switch of term * term ID.Map.t (* switch on constants *)
  | Bind of binder * var * term
  | Let of var * term * term
  | Not of term
  | Binop of binop * term * term
  | Asserting of term * term
  | Undefined_value
  | Bool of bool

and select = {
  select_name: ID.t lazy_t;
  select_cstor: ID.t;
  select_i: int;
}

type definition = ID.t * Ty.t * term

type statement =
  | Data of Ty.data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of definition list
  | Assert of term
  | Goal of var list * term

(** {2 Helper} *)

let unfold_fun t =
  let rec aux acc t = match t.term with
    | Bind (Fun, v, t') -> aux (v::acc) t'
    | _ -> List.rev acc, t
  in
  aux [] t

(* TODO *)

let pp_term out _ = Fmt.string out "todo:term"

let pp_ty out _ = Fmt.string out "todo:ty"

let pp_statement out _ = Fmt.string out "todo:stmt"

(** {2 Constructors} *)

let term_view t = t.term

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty
    then app_ty_ ty_rest tail
    else Ty.ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.pp ty_a pp_term a Ty.pp a.ty
  | (Ty.Prop | Ty.Const _), a::_ ->
    Ty.ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.pp ty pp_term a

let mk_ term ty = {term; ty}
let ty t = t.ty

let true_ = mk_ (Bool true) Ty.prop
let false_ = mk_ (Bool false) Ty.prop
let undefined_value ty = mk_ Undefined_value ty

let asserting t g =
  if not (Ty.equal Ty.prop g.ty) then (
    Ty.ill_typed "asserting: test  must have type prop, not `@[%a@]`" Ty.pp g.ty;
  );
  mk_ (Asserting (t,g)) t.ty

let var v = mk_ (Var v) (Var.ty v)
let unknown v = mk_ (Unknown v) (Var.ty v)

let const id ty = mk_ (Const id) ty

let select (s:select) (t:term) ty = mk_ (Select (s,t)) ty

let app f l = match f.term, l with
  | _, [] -> f
  | App (f1, l1), _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f1, l1 @ l)) ty
  | _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f, l)) ty

let app_a f a = app f (Array.to_list a)

let if_ a b c =
  if a.ty <> Ty.Prop
  then Ty.ill_typed "if: test  must have type prop, not `@[%a@]`" Ty.pp a.ty;
  if not (Ty.equal b.ty c.ty)
  then Ty.ill_typed
      "if: both branches must have same type,@ not `@[%a@]` and `@[%a@]`"
      Ty.pp b.ty Ty.pp c.ty;
  mk_ (If (a,b,c)) b.ty

let match_ t m =
  let c1, (_, rhs1) = ID.Map.choose m in
  ID.Map.iter
    (fun c (_, rhs) ->
       if not (Ty.equal rhs1.ty rhs.ty)
       then Ty.ill_typed
           "match: cases %a and %a disagree on return type,@ \
           between %a and %a"
           ID.pp c1 ID.pp c Ty.pp rhs1.ty Ty.pp rhs.ty)
    m;
  mk_ (Match (t,m)) rhs1.ty

let switch u m =
  try
    let _, t1 = ID.Map.choose m in
    mk_ (Switch (u,m)) t1.ty
  with Not_found ->
    invalid_arg "Ast.switch: empty list of cases"

let let_ v t u =
  if not (Ty.equal (Var.ty v) t.ty)
  then Ty.ill_typed
      "let: variable %a : @[%a@]@ and bounded term : %a@ should have same type"
      Var.pp v Ty.pp (Var.ty v) Ty.pp t.ty;
  mk_ (Let (v,t,u)) u.ty

let bind ~ty b v t = mk_ (Bind(b,v,t)) ty

let fun_ v t =
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Bind (Fun,v,t)) ty

let quant_ q v t =
  if not (Ty.equal t.ty Ty.prop) then (
    Ty.ill_typed
      "quantifier: bounded term : %a@ should have type prop"
      Ty.pp t.ty;
  );
  let ty = Ty.prop in
  mk_ (q v t) ty

let forall = quant_ (fun v t -> Bind (Forall,v,t))
let exists = quant_ (fun v t -> Bind (Exists,v,t))

let mu v t =
  if not (Ty.equal (Var.ty v) t.ty)
  then Ty.ill_typed "mu-term: var has type %a,@ body %a"
      Ty.pp (Var.ty v) Ty.pp t.ty;
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Bind (Fun,v,t)) ty

let fun_l = List.fold_right fun_
let fun_a = Array.fold_right fun_
let forall_l = List.fold_right forall
let exists_l = List.fold_right exists

let eq a b =
  if not (Ty.equal a.ty b.ty)
  then Ty.ill_typed "eq: `@[%a@]` and `@[%a@]` do not have the same type"
      pp_term a pp_term b;
  mk_ (Binop (Eq,a,b)) Ty.prop

let check_prop_ t =
  if not (Ty.equal t.ty Ty.prop)
  then Ty.ill_typed "expected prop, got `@[%a : %a@]`" pp_term t Ty.pp t.ty

let binop op a b = mk_ (Binop (op, a, b)) Ty.prop
let binop_prop op a b =
  check_prop_ a; check_prop_ b;
  binop op a b

let and_ = binop_prop And
let or_ = binop_prop Or
let imply = binop_prop Imply

let and_l = function
  | [] -> true_
  | [f] -> f
  | a :: l -> List.fold_left and_ a l

let or_l = function
  | [] -> false_
  | [f] -> f
  | a :: l -> List.fold_left or_ a l

let not_ t =
  check_prop_ t;
  mk_ (Not t) Ty.prop

(** {2 Environment} *)

type env_entry =
  | E_uninterpreted_ty
  | E_uninterpreted_cst (* domain element *)
  | E_const of Ty.t
  | E_data of Ty.t ID.Map.t (* list of cstors *)
  | E_cstor of Ty.t (* datatype it belongs to *)
  | E_defined of Ty.t * term (* if defined *)

type env = {
  defs: env_entry ID.Map.t;
}
(** Environment with definitions and goals *)

let env_empty = {
  defs=ID.Map.empty;
}

let add_def id def env = { defs=ID.Map.add id def env.defs}

let env_add_statement env st =
  match st with
    | Data l ->
      List.fold_left
        (fun env {Ty.data_id; data_cstors} ->
           let map = add_def data_id (E_data data_cstors) env in
           ID.Map.fold
             (fun c_id c_ty map -> add_def c_id (E_cstor c_ty) map)
             data_cstors map)
        env l
    | TyDecl id -> add_def id E_uninterpreted_ty env
    | Decl (id,ty) -> add_def id (E_const ty) env
    | Define l ->
      List.fold_left
        (fun map (id,ty,def) -> add_def id (E_defined (ty,def)) map)
        env l
    | Goal _
    | Assert _ -> env

let env_of_statements seq =
  Sequence.fold env_add_statement env_empty seq

let env_find_def env id =
  try Some (ID.Map.find id env.defs)
  with Not_found -> None

let env_add_def env id def = add_def id def env
