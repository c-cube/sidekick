
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Fmt = CCFormat

type 'a or_error = ('a, string) CCResult.t

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
    | App of ID.t * t list
    | Arrow of t * t

  let prop = Prop
  let app id l = App (id,l)
  let const id = app id []
  let arrow a b = Arrow (a,b)
  let arrow_l = List.fold_right arrow

  let int = const ID.B.int
  let rat = const ID.B.rat

  let to_int_ = function
    | Prop -> 0
    | App _ -> 1
    | Arrow _ -> 2

  let (<?>) = CCOrd.(<?>)

  let rec compare a b = match a, b with
    | Prop, Prop -> 0
    | App (a,la), App (b,lb) ->
      CCOrd.(ID.compare a b <?> (list compare, la, lb))
    | Arrow (a1,a2), Arrow (b1,b2) ->
      compare a1 b1 <?> (compare, a2,b2)
    | Prop, _
    | App _, _
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
    | App (id,[]) -> ID.pp out id
    | App (id,l) -> Fmt.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list pp) l
    | Arrow _ as ty ->
      let args, ret = unfold ty in
      Fmt.fprintf out "(@[-> %a@ %a@])"
        (Util.pp_list ~sep:" " pp) args pp ret

  (** {2 Datatypes} *)

  type data = {
    data_id: ID.t;
    data_cstors: t ID.Map.t;
  }

  module Map = CCMap.Make(struct
      type _t = t
      type t = _t
      let compare = compare
    end)

  let ill_typed fmt =
    Error.errorf ("ill-typed: " ^^ fmt)
end

type var = Ty.t Var.t

type op =
  | And
  | Or
  | Imply
  | Eq
  | Distinct

type arith_op =
  | Leq
  | Lt
  | Geq
  | Gt
  | Add
  | Minus
  | Mult
  | Div

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
  | Num_z of Z.t
  | Num_q of Q.t
  | App of term * term list
  | If of term * term * term
  | Match of term * (var list * term) ID.Map.t
  | Select of select * term
  | Bind of binder * var * term
  | Arith of arith_op * term list
  | Let of (var * term) list * term
  | Not of term
  | Op of op * term list
  | Asserting of {t: term; guard: term}
  | Undefined_value
  | Bool of bool

and select = {
  select_name: ID.t lazy_t;
  select_cstor: ID.t;
  select_i: int;
}


type definition = ID.t * Ty.t * term

type statement =
  | SetLogic of string
  | SetOption of string list
  | SetInfo of string list
  | Data of Ty.data list
  | TyDecl of ID.t * int (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of definition list
  | Assert of term
  | Assert_bool of int list
  | Goal of var list * term
  | CheckSat
  | Exit

(** {2 Helpers} *)

let is_true = function {term=Bool true;_} -> true | _ -> false
let is_false = function {term=Bool false;_} -> true | _ -> false

let unfold_binder b t =
  let rec aux acc t = match t.term with
    | Bind (b', v, t') when b=b' -> aux (v::acc) t'
    | _ -> List.rev acc, t
  in
  aux [] t

let unfold_fun = unfold_binder Fun

let pp_binder out = function
  | Forall -> Fmt.string out "forall"
  | Exists -> Fmt.string out "exists"
  | Fun -> Fmt.string out "lambda"
  | Mu -> Fmt.string out "mu"

let pp_op out = function
  | And -> Fmt.string out "and"
  | Or -> Fmt.string out "or"
  | Imply -> Fmt.string out "=>"
  | Eq -> Fmt.string out "="
  | Distinct -> Fmt.string out "distinct"

let pp_arith out = function
  | Leq -> Fmt.string out "<="
  | Lt -> Fmt.string out "<"
  | Geq -> Fmt.string out ">="
  | Gt -> Fmt.string out ">"
  | Add -> Fmt.string out "+"
  | Minus -> Fmt.string out "-"
  | Mult -> Fmt.string out "*"
  | Div -> Fmt.string out "/"

let pp_term =
  let rec pp out t = match t.term with
    | Var v -> Var.pp out v
    | Const id -> ID.pp out id
    | App (f, l) -> Fmt.fprintf out "(@[<hv1>%a@ %a@])" pp f (Util.pp_list pp) l
    | If (a,b,c) -> Fmt.fprintf out "(@[<hv>ite@ %a@ %a@ %a@])" pp a pp b pp c
    | Match (u, m) ->
      let pp_case out (id,(vars,rhs)) =
        if vars=[] then Fmt.fprintf out "(@[<2>case %a@ %a@])" ID.pp id pp rhs
        else Fmt.fprintf out "(@[<2>case (@[%a@ %a@])@ %a@])"
            ID.pp id (Util.pp_list Var.pp) vars pp rhs
      in
      Fmt.fprintf out "(@[<hv2>match %a@ %a@])"
        pp u (Util.pp_list pp_case) (ID.Map.to_list m)
    | Select (s, t) ->
      Fmt.fprintf out "(@[select_%a_%d@ %a@])"
        ID.pp s.select_cstor s.select_i pp t
    | Bool b -> Fmt.fprintf out "%B" b
    | Not t -> Fmt.fprintf out "(@[<1>not@ %a@])" pp t
    | Op (o,l) -> Fmt.fprintf out "(@[<hv1>%a@ %a@])" pp_op o (Util.pp_list pp) l
    | Bind (b,v,u) ->
      Fmt.fprintf out "(@[<1>%a ((@[%a@ %a@]))@ %a@])"
        pp_binder b Var.pp v Ty.pp (Var.ty v) pp u
    | Let (vbs,u) ->
      Fmt.fprintf out "(@[<1>let (@[%a@])@ %a@])" pp_vbs vbs pp u
    | Num_z z -> Z.pp_print out z
    | Num_q z -> Q.pp_print out z
    | Arith (op, l) ->
      Fmt.fprintf out "(@[<hv>%a@ %a@])" pp_arith op (Util.pp_list pp) l
    | Undefined_value -> Fmt.string out "<undefined>"
    | Asserting {t;guard} ->
      Fmt.fprintf out "(@[asserting@ %a@ %a@])" pp t pp guard

  and pp_vbs out l =
    let pp_vb out (v,t) = Fmt.fprintf out "(@[%a@ %a@])" Var.pp v pp t in
    Util.pp_list pp_vb out l
  in pp

let pp_ty = Ty.pp

(** {2 Constructors} *)

let term_view t = t.term

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty
    then app_ty_ ty_rest tail
    else Ty.ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.pp ty_a pp_term a Ty.pp a.ty
  | (Ty.Prop | Ty.App _), a::_ ->
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
  mk_ (Asserting {t;guard=g}) t.ty

let var v = mk_ (Var v) (Var.ty v)
let const id ty = mk_ (Const id) ty

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

let let_l vbs t = match vbs with
  | [] -> t
  | _::_ ->
    List.iter
      (fun (v,t) ->
        if not (Ty.equal (Var.ty v) t.ty) then (
          Ty.ill_typed
            "let: variable %a : @[%a@]@ and bounded term : %a@ should have same type"
            Var.pp v Ty.pp (Var.ty v) Ty.pp t.ty;
        );)
      vbs;
    mk_ (Let (vbs,t)) t.ty

let let_ v t u = let_l [v,t] u

let bind ~ty b v t = mk_ (Bind(b,v,t)) ty

let select ~ty (s:select) (t:term) = mk_ (Select (s,t)) ty

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
  mk_ (Op (Eq,[a;b])) Ty.prop

let check_prop_ t =
  if not (Ty.equal t.ty Ty.prop) then (
    Ty.ill_typed "expected prop, got `@[%a : %a@]`" pp_term t Ty.pp t.ty
  )

let op op l = mk_ (Op (op, l)) Ty.prop
let binop_prop o a b =
  check_prop_ a; check_prop_ b;
  op o [a;b]

let and_ = binop_prop And
let or_ = binop_prop Or
let imply = binop_prop Imply

let and_l = function
  | [] -> true_
  | [f] -> f
  | l -> op And l

let or_l = function
  | [] -> false_
  | [f] -> f
  | l -> op Or l

let not_ t =
  check_prop_ t;
  mk_ (Not t) Ty.prop

let arith ty op l = mk_ (Arith (op,l)) ty

let num_q ty z = mk_ (Num_q z) ty
let num_z ty z = mk_ (Num_z z) ty

let parse_num ~where (s:string) : [`Q of Q.t | `Z of Z.t] =
  let fail() =
    Error.errorf "%sexpected number, got `%s`" (Lazy.force where) s
  in
  begin match Z.of_string s with
    | n -> `Z n
    | exception _ ->
      begin match Q.of_string s with
        | n -> `Q n
        | exception _ ->
          if String.contains s '.' then (
            let p1, p2 = CCString.Split.left_exn ~by:"." s in
            let n1, n2 =
              try Z.of_string p1, Z.of_string p2
              with _ -> fail()
            in
            let factor_10 = Z.pow (Z.of_int 10) (String.length p2) in
            (* [(p1·10^{length p2}+p2) / 10^{length p2}] *)
            let n =
              Q.div
                (Q.of_bigint (Z.add n2 (Z.mul n1 factor_10)))
                (Q.of_bigint factor_10)
            in
            `Q n
          ) else fail()
      end
  end

let num_str ty s =
  begin match parse_num ~where:(Lazy.from_val "") s with
    | `Q x -> num_q ty x
    | `Z x -> num_z ty x
  end

(** {2 More IO} *)

let pp_statement out = function
  | SetLogic s -> Fmt.fprintf out "(set-logic %s)" s
  | SetOption l -> Fmt.fprintf out "(@[set-logic@ %a@])" (Util.pp_list Fmt.string) l
  | SetInfo l -> Fmt.fprintf out "(@[set-info@ %a@])" (Util.pp_list Fmt.string) l
  | CheckSat -> Fmt.string out "(check-sat)"
  | TyDecl (s,n) -> Fmt.fprintf out "(@[declare-sort@ %a %d@])" ID.pp s n
  | Decl (id,ty) ->
    let args, ret = Ty.unfold ty in
    Fmt.fprintf out "(@[<1>declare-fun@ %a (@[%a@])@ %a@])"
      ID.pp id (Util.pp_list Ty.pp) args Ty.pp ret
  | Assert t -> Fmt.fprintf out "(@[assert@ %a@])" pp_term t
  | Assert_bool l -> Fmt.fprintf out "(@[assert-bool@ %a@])" (Util.pp_list Fmt.int) l
  | Goal (vars,g) ->
    Fmt.fprintf out "(@[assert-not@ %a@])" pp_term (forall_l vars (not_ g))
  | Exit -> Fmt.string out "(exit)"
  | Data _ -> assert false (* TODO *)
  | Define _ -> assert false (* TODO *)

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
    | TyDecl (id,_) -> add_def id E_uninterpreted_ty env
    | Decl (id,ty) -> add_def id (E_const ty) env
    | Define l ->
      List.fold_left
        (fun map (id,ty,def) -> add_def id (E_defined (ty,def)) map)
        env l
    | Goal _ | Assert _ | Assert_bool _ | CheckSat | Exit
    | SetLogic _ | SetOption _ | SetInfo _
      -> env

let env_of_statements seq =
  Sequence.fold env_add_statement env_empty seq

let env_find_def env id =
  try Some (ID.Map.find id env.defs)
  with Not_found -> None

let env_add_def env id def = add_def id def env
