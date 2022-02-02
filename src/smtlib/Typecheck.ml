(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open! Sidekick_base
module Loc = Smtlib_utils.V_2_6.Loc

module PA = Smtlib_utils.V_2_6.Ast
module BT = Sidekick_base
module Ty = BT.Ty
module T = BT.Term
module Fun = BT.Fun
module Form = BT.Form
module Stmt = BT.Statement

type 'a or_error = ('a, string) CCResult.t

let pp_loc_opt = Loc.pp_opt

(** {2 Parsing} *)

module StrTbl = CCHashtbl.Make(CCString)

module Ctx = struct
  type kind =
    | K_ty of ty_kind
    | K_fun of Fun.t

  and ty_kind =
    | K_atomic of Ty.def

  type t = {
    tst: T.store;
    names: (ID.t * kind) StrTbl.t;
    lets: T.t StrTbl.t;
    mutable loc: Loc.t option; (* current loc *)
  }

  let create (tst:T.store) : t = {
    tst;
    names=StrTbl.create 64;
    lets=StrTbl.create 16;
    loc=None;
  }

  let loc t = t.loc
  let set_loc ?loc t = t.loc <- loc

  let add_id_ self (s:string) (id:ID.t) (k:kind) : unit =
    StrTbl.add self.names s (id,k);
    ()

  (* locally bind [bs] and call [f], then remove bindings *)
  let with_lets (self:t) (bs:(string*T.t) list) (f:unit -> 'a): 'a =
    List.iter (fun (v,u) -> StrTbl.add self.lets v u) bs;
    CCFun.finally ~f
      ~h:(fun () ->
          List.iter (fun (v,_) -> StrTbl.remove self.lets v) bs)

  let find_ty_def self (s:string) : Ty.def =
    match StrTbl.get self.names s with
    | Some (_, K_ty (K_atomic def)) -> def
    | _ -> Error.errorf "expected %s to be an atomic type" s
end

let errorf_ctx ctx msg =
  Error.errorf ("at %a:@ " ^^ msg) pp_loc_opt (Ctx.loc ctx)

let ill_typed ctx fmt =
  errorf_ctx ctx ("ill-typed: " ^^ fmt)

let check_bool_ ctx t =
  if not (Ty.equal (T.ty t) (Ty.bool())) then (
    ill_typed ctx "expected bool, got `@[%a : %a@]`" T.pp t Ty.pp (T.ty t)
  )

let find_id_ ctx (s:string): ID.t * Ctx.kind =
  try StrTbl.find ctx.Ctx.names s
  with Not_found -> errorf_ctx ctx "name `%s` not in scope" s

(* parse a type *)
let rec conv_ty ctx (t:PA.ty) : Ty.t = match t with
  | PA.Ty_bool -> Ty.bool()
  | PA.Ty_real -> Ty.real()
  | PA.Ty_app ("Int",[]) -> Ty.int()
  | PA.Ty_app (f, l) ->
    let def = Ctx.find_ty_def ctx f in
    let l = List.map (conv_ty ctx) l in
    Ty.atomic def l
  | PA.Ty_arrow _ ->
    ill_typed ctx "cannot handle arrow types"

let is_num s =
  let is_digit_or_dot = function '0' .. '9' | '.' -> true | _ -> false in
  if s.[0] = '-'
  then CCString.for_all is_digit_or_dot (String.sub s 1 (String.length s-1))
  else CCString.for_all is_digit_or_dot s

let string_as_z (s:string) : Z.t option =
  try Some (Z.of_string s)
  with _ -> None

let string_as_q (s:string) : Q.t option =
  try
    let x =
      try Q.of_string s
      with _ ->
        let f = float_of_string s in
        Q.of_float f
    in
    Some x
  with _ -> None

let t_as_q t = match Term.view t with
  | T.LRA (Const n) -> Some n
  | T.LIA (Const n) -> Some (Q.of_bigint n)
  | _ -> None

let t_as_z t = match Term.view t with
  | T.LIA (Const n) -> Some n
  | _ -> None

let is_real t =
  match T.view t with
  | T.LRA _ -> true
  | _ -> Ty.equal (T.ty t) (Ty.real())

(* convert [t] to a real term *)
let cast_to_real (ctx:Ctx.t) (t:T.t) : T.t =
  let rec conv t =
    match T.view t with
    | T.LRA _ -> t
    | _ when Ty.equal (T.ty t) (Ty.real()) -> t
    | T.LIA (Const n) ->
      T.lra ctx.tst (Const (Q.of_bigint n))
    | T.LIA l ->
      (* convert the whole structure to reals *)
      let l = LIA_view.to_lra conv l in
      T.lra ctx.tst l
    | _ ->
      errorf_ctx ctx "cannot cast term to real@ :term %a" T.pp t
  in
  conv t

let conv_arith_op (ctx:Ctx.t) t (op:PA.arith_op) (l:T.t list) : T.t =
  let tst = ctx.Ctx.tst in

  let mk_pred p a b =
    if is_real a||is_real b
    then T.lra tst (Pred (p, cast_to_real ctx a, cast_to_real ctx b))
    else T.lia tst (Pred (p, a, b))
  and mk_op o a b =
    if is_real a||is_real b
    then T.lra tst (Op (o, cast_to_real ctx a, cast_to_real ctx b))
    else T.lia tst (Op (o, a, b))
  in

  begin match op, l with
    | PA.Leq, [a;b] -> mk_pred Leq a b
    | PA.Lt, [a;b] -> mk_pred Lt a b
    | PA.Geq, [a;b] -> mk_pred Geq a b
    | PA.Gt, [a;b] -> mk_pred Gt a b
    | PA.Add, [a;b] -> mk_op Plus a b
    | PA.Add, (a::l) ->
      List.fold_left (fun a b -> mk_op Plus a b) a l
    | PA.Minus, [a] ->
      begin match t_as_q a, t_as_z a with
        | _, Some n -> T.lia tst (Const (Z.neg n))
        | Some q, None -> T.lra tst (Const (Q.neg q))
        | None, None ->
          let zero =
            if is_real a then T.lra tst (Const Q.zero)
            else T.lia tst (Const Z.zero)
          in

          mk_op Minus zero a
      end
    | PA.Minus, [a;b] -> mk_op Minus a b
    | PA.Minus, (a::l) ->
      List.fold_left (fun a b -> mk_op Minus a b) a l

    | PA.Mult, [a;b] when is_real a || is_real b ->
      begin match t_as_q a, t_as_q b with
        | Some a, Some b -> T.lra tst (Const (Q.mul a b))
        | Some a, _ -> T.lra tst (Mult (a, b))
        | _, Some b -> T.lra tst (Mult (b, a))
        | None, None ->
          errorf_ctx ctx "cannot handle non-linear mult %a" PA.pp_term t
      end

    | PA.Mult, [a;b] ->
      begin match t_as_z a, t_as_z b with
        | Some a, Some b -> T.lia tst (Const (Z.mul a b))
        | Some a, _ -> T.lia tst (Mult (a, b))
        | _, Some b -> T.lia tst (Mult (b, a))
        | None, None ->
          errorf_ctx ctx "cannot handle non-linear mult %a" PA.pp_term t
      end

    | PA.Div, [a;b] when is_real a || is_real b ->
      begin match t_as_q a, t_as_q b with
        | Some a, Some b -> T.lra tst (Const (Q.div a b))
        | _, Some b -> T.lra tst (Mult (Q.inv b, a))
        | _, None ->
          errorf_ctx ctx "cannot handle non-linear div %a" PA.pp_term t
      end

    | PA.Div, [a;b] ->
      (* becomes a real *)
      begin match t_as_q a, t_as_q b with
        | Some a, Some b -> T.lra tst (Const (Q.div a b))
        | _, Some b ->
          let a = cast_to_real ctx a in
          T.lra tst (Mult (Q.inv b, a))
        | _, None ->
          errorf_ctx ctx "cannot handle non-linear div %a" PA.pp_term t
      end

    | _ ->
      errorf_ctx ctx "cannot handle arith construct %a" PA.pp_term t
  end

(* conversion of terms *)
let rec conv_term (ctx:Ctx.t) (t:PA.term) : T.t =
  let tst = ctx.Ctx.tst in
  match t with
  | PA.True -> T.true_ tst
  | PA.False -> T.false_ tst
  | PA.Const s when is_num s ->
    begin match string_as_z s with
      | Some n -> T.lia tst (Const n)
      | None ->
        begin match string_as_q s with
          | Some n -> T.lra tst (Const n)
          | None -> errorf_ctx ctx "expected a number for %a" PA.pp_term t
        end
    end
  | PA.Const f
  | PA.App (f, []) ->
    (* lookup in `let` table, then in type defs *)
    begin match StrTbl.find ctx.Ctx.lets f with
      | u -> u
      | exception Not_found ->
        begin match find_id_ ctx f with
          | _, Ctx.K_fun f -> T.const tst f
          | _, Ctx.K_ty _ ->
            errorf_ctx ctx "expected term, not type; got `%s`" f
        end
    end
  | PA.App ("xor", [a;b]) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    Form.xor ctx.Ctx.tst a b
  | PA.App (f, args) ->
    let args = List.map (conv_term ctx) args in
    begin match find_id_ ctx f with
      | _, Ctx.K_fun f -> T.app_fun tst f (IArray.of_list args)
      | _, Ctx.K_ty _ ->
        errorf_ctx ctx "expected function, got type `%s` instead" f
    end
  | PA.If (a,b,c) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    Form.ite tst a b c
  | PA.Fun _ | PA.Forall _ | PA.Exists _ ->
    errorf_ctx ctx "cannot process lambda/quantifiers in %a" PA.pp_term t
  | PA.Let (vbs, body) ->
    let bs =
      List.map
        (fun (v,u) ->
           let u = conv_term ctx u in
           v, u)
        vbs
    in
    Ctx.with_lets ctx bs (fun () -> conv_term ctx body)
  | PA.Distinct l ->
    let l = List.map (conv_term ctx) l in
    Form.distinct_l tst l
  | PA.And l ->
    let l = List.map (conv_term ctx) l in
    Form.and_l tst l
  | PA.Or l ->
    let l = List.map (conv_term ctx) l in
    Form.or_l tst l
  | PA.Not a ->
    let a = conv_term ctx a in
    Form.not_ tst a
  | PA.Eq (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    Form.eq tst a b
  | PA.Imply (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    Form.imply tst a b
  | PA.Is_a (s, u) ->
    let u = conv_term ctx u in
    begin match find_id_ ctx s with
      | _, Ctx.K_fun {Fun.fun_view=Base_types.Fun_cstor c; _} ->
        Term.is_a tst c u
      | _ -> errorf_ctx ctx "expected `%s` to be a constructor" s
    end
  | PA.Match (_lhs, _l) ->
    errorf_ctx ctx "TODO: support match in %a" PA.pp_term t
    (* FIXME: do that properly, using [with_lets] with selectors
    (* convert a regular case *)
    let conv_case c vars rhs =
      let c_id = find_id_ ctx c in
      (* obtain the type *)
      let ty_args, _ty_ret = match Ctx.find_kind ctx c_id with
       | Ctx.K_cstor ty -> Ty.unfold ty
       | _ ->
         errorf_ctx ctx "expected `@[%a@]`@ to be a constructor" ID.pp c_id
      in
      (* pair variables with their type *)
      if List.length vars <> List.length ty_args then (
       errorf_ctx ctx
         "in @[%a@] for case %a,@ wrong number of arguments (expected %d)"
         PA.pp_term t ID.pp c_id (List.length ty_args);
      );
      let vars = List.combine vars ty_args in
      Ctx.with_vars ctx vars
       (fun vars ->
          let rhs = conv_term ctx rhs in
          c_id, vars, rhs)
     in
     (* convert default case, where [m] contains the partial map. We have
     to complete this map *)
     let lhs = conv_term ctx lhs in
     let default, cases =
     List.fold_left
      (fun (def,cases) branch -> match branch with
         | PA.Match_case (c,vars,rhs) ->
           let c, vars, rhs = conv_case c vars rhs in
           (* no duplicate *)
           if ID.Map.mem c cases
           then errorf_ctx ctx "constructor %a occurs twice" ID.pp c;
           def, ID.Map.add c (vars,rhs) cases
        | PA.Match_default rhs ->
          (* check there is only one "default" case *)
          begin match def with
            | Some _ -> errorf_ctx ctx "cannot have two `default` cases"
            | None ->
              let rhs = conv_term ctx rhs in
              Some rhs, cases
          end)
      (None,ID.Map.empty) l
     in
     (* now fill the blanks, check exhaustiveness *)
     let all_cstors = Ctx.as_data ctx lhs.A.ty in
     let cases = match default with
     | None ->
      (* check exhaustiveness *)
      let missing =
        all_cstors
        |> List.filter (fun (cstor,_) -> not (ID.Map.mem cstor cases))
        |> List.map fst
      in
      if missing<>[] then (
        errorf_ctx ctx
          "missing cases in `@[%a@]`: @[%a@]"
          PA.pp_term t (Util.pp_list ID.pp) missing;
      );
      cases
     | Some def_rhs ->
      List.fold_left
        (fun cases (cstor,ty_cstor) ->
           if ID.Map.mem cstor cases then cases
           else (
             let args, _ = Ty.unfold ty_cstor in
             let vars = List.mapi (fun i ty -> A.Var.makef ~ty "_%d" i) args in
             ID.Map.add cstor (vars, def_rhs) cases
           ))
        cases all_cstors
     in
     A.match_ lhs cases
       *)
  | PA.Arith (op, l) ->
    let l = List.map (conv_term ctx) l in
    conv_arith_op ctx t op l

  | PA.Cast (t, ty_expect) ->
    let t = conv_term ctx t in
    let ty_expect = conv_ty ctx ty_expect in
    if not (Ty.equal (T.ty t) ty_expect) then (
      ill_typed ctx "term `%a`@ should have type `%a`" T.pp t Ty.pp ty_expect
    );
    t
  | PA.Attr (t, [":named",_]) -> conv_term ctx t
  | _ ->
    errorf_ctx ctx "unsupported term %a" PA.pp_term t

let conv_fun_decl ctx f : string * Ty.t list * Ty.t =
  if f.PA.fun_ty_vars <> [] then (
    errorf_ctx ctx "cannot convert polymorphic function@ %a"
      (PA.pp_fun_decl PA.pp_ty) f
  );
  let args = List.map (conv_ty ctx) f.PA.fun_args in
  let ret = conv_ty ctx f.PA.fun_ret in
  f.PA.fun_name, args, ret

(* FIXME: fun defs
let conv_fun_def ctx f_decl body : string * Ty.t * (unit -> T.t) =
  if f_decl.PA.fun_ty_vars <> [] then (
    errorf_ctx ctx "cannot convert polymorphic function@ %a"
      (PA.pp_fun_decl PA.pp_typed_var) f_decl;
  );
  let args = conv_vars ctx f_decl.PA.fun_args in
  let ty =
      (List.map snd args)
      (conv_ty_fst ctx f_decl.PA.fun_ret)
  in
  (* delayed body, for we need to declare the functions in the recursive block first *)
  let conv_body() =
    Ctx.with_vars ctx args
      (fun args ->
         A.fun_l args (conv_term ctx body))
  in
  f_decl.PA.fun_name, ty, conv_body

let conv_fun_defs ctx decls bodies : A.definition list =
  let l = List.map2 (conv_fun_def ctx) decls bodies in
  let ids = List.map (fun (f,ty,_) -> Ctx.add_id ctx f (Ctx.K_fun ty)) l in
  let defs = List.map2 (fun id (_,ty,body) -> id, ty, body()) ids l in
  (* parse id,ty and declare them before parsing the function bodies *)
  defs
   *)

let rec conv_statement ctx (s:PA.statement): Stmt.t list =
  Log.debugf 4 (fun k->k "(@[<1>statement_of_ast@ %a@])" PA.pp_stmt s);
  Ctx.set_loc ctx ?loc:(PA.loc s);
  conv_statement_aux ctx s

and conv_statement_aux ctx (stmt:PA.statement) : Stmt.t list =
  let tst = ctx.Ctx.tst in
  match PA.view stmt with
  | PA.Stmt_set_logic s -> [Stmt.Stmt_set_logic s]
  | PA.Stmt_set_option l -> [Stmt.Stmt_set_option l]
  | PA.Stmt_set_info (a,b) -> [Stmt.Stmt_set_info (a,b)]
  | PA.Stmt_exit -> [Stmt.Stmt_exit]
  | PA.Stmt_decl_sort (s,n) ->
    let id = ID.make s in
    Ctx.add_id_ ctx s id
      (Ctx.K_ty (Ctx.K_atomic (Ty.Ty_uninterpreted id)));
    [Stmt.Stmt_ty_decl (id, n)]
  | PA.Stmt_decl fr ->
    let f, args, ret = conv_fun_decl ctx fr in
    let id = ID.make f in
    Ctx.add_id_ ctx f id
      (Ctx.K_fun (Fun.mk_undef' id args ret));
    [Stmt.Stmt_decl (id, args,ret)]
  | PA.Stmt_data l ->
    (* first, read and declare each datatype (it can occur in the other
      datatypes' constructors) *)
    (* TODO:remove
    let pre_parse ((data_name,arity),cases) =
      if arity <> 0 then (
        errorf_ctx ctx "cannot handle polymorphic datatype %s" data_name;
      );
      let data_id = Ctx.add_id ctx data_name (Ctx.K_ty Ctx.K_data) in
      data_id, cases
    in
    let l = List.map pre_parse l in
       *)
    let module Cstor = Base_types.Cstor in
    let cstors_of_data data (cstors:PA.cstor list) : Cstor.t ID.Map.t =
      let parse_case {PA.cstor_name; cstor_args; cstor_ty_vars} =
        if cstor_ty_vars <> [] then (
          errorf_ctx ctx "cannot handle polymorphic constructor %s" cstor_name;
        );
        let cstor_id = ID.make cstor_name in
        (* how to translate selectors *)
        let mk_selectors (cstor:Cstor.t) =
          List.mapi
            (fun i (name,ty) ->
               let select_id = ID.make name in
               let sel = {
                 Select.
                 select_id;
                 select_ty=lazy (conv_ty ctx ty);
                 select_cstor=cstor;
                 select_i=i;
               } in
               (* now declare the selector *)
               Ctx.add_id_ ctx name select_id
                 (Ctx.K_fun (Fun.select sel));
               sel)
            cstor_args
        in
        let rec cstor = {
          Cstor.
          cstor_id;
          cstor_is_a = ID.makef "(is _ %s)" cstor_name; (* every fun needs a name *)
          cstor_args=lazy (mk_selectors cstor);
          cstor_arity=0;
          cstor_ty_as_data=data;
          cstor_ty=data.Base_types.data_as_ty;
        } in
        (* declare cstor *)
        Ctx.add_id_ ctx cstor_name cstor_id (Ctx.K_fun (Fun.cstor cstor));
        cstor_id, cstor
      in
      let cstors = List.map parse_case cstors in
      ID.Map.of_list cstors
    in
    (* now parse constructors *)
    let l =
     List.map
       (fun ((data_name,arity), (cstors:PA.cstor list)) ->
         if arity <> 0 then (
           (* TODO: handle poly datatypes properly *)
           errorf_ctx ctx "cannot handle polymorphic datatype %s" data_name;
         );
         let data_id = ID.make data_name in
         let rec data = {
           Data.
           data_id;
           data_cstors=lazy (cstors_of_data data cstors);
           data_as_ty=lazy (
             let def = Ty.Ty_data { data; } in
             Ty.atomic def []
           );
         } in
         Ctx.add_id_ ctx data_name data_id
           (Ctx.K_ty (Ctx.K_atomic (Ty.Ty_data {data})));
         data)
      l
    in
    (* now force definitions *)
    List.iter
      (fun {Data.data_cstors=lazy m;data_as_ty=lazy _;_} ->
         ID.Map.iter (fun _ ({Cstor.cstor_args=lazy l;_} as r) -> r.Base_types.cstor_arity <- List.length l) m;
         ())
      l;
    [Stmt.Stmt_data l]
  | PA.Stmt_funs_rec _defs ->
    errorf_ctx ctx "not implemented: definitions" PA.pp_stmt stmt
      (* TODO
    let {PA.fsr_decls=decls; fsr_bodies=bodies} = defs in
    if List.length decls <> List.length bodies then (
      errorf_ctx ctx "declarations and bodies should have same length";
    );
    let defs = conv_fun_defs ctx decls bodies in
    [A.Define defs]
         *)
  | PA.Stmt_fun_def
      {PA.fr_decl={PA.fun_ty_vars=[]; fun_args=[]; fun_name; fun_ret}; fr_body} ->
    (* turn [def f : ret := body] into [decl f : ret; assert f=body] *)
    let ret = conv_ty ctx fun_ret in
    let id = ID.make fun_name in
    let f = Fun.mk_undef_const id ret in
    Ctx.add_id_ ctx fun_name id (Ctx.K_fun f);
    let rhs = conv_term ctx fr_body in
    [ Stmt.Stmt_decl (id,[],ret);
      Stmt.Stmt_assert (Form.eq tst (T.const tst f) rhs);
    ]
  | PA.Stmt_fun_rec _
  | PA.Stmt_fun_def _
    -> errorf_ctx ctx "unsupported definition: %a" PA.pp_stmt stmt
  | PA.Stmt_assert t ->
    let t = conv_term ctx t in
    check_bool_ ctx t;
    [Stmt.Stmt_assert t]
  | PA.Stmt_check_sat -> [Stmt.Stmt_check_sat []]
  | PA.Stmt_check_sat_assuming l ->
    let l =
      List.map
        (fun (t,b) ->
           let t = conv_term ctx (PA.const t) in
           check_bool_ ctx t;
           b,t)
        l
    in
    [Stmt.Stmt_check_sat l]
  | PA.Stmt_get_model -> [Stmt.Stmt_get_model]
  | PA.Stmt_get_value l ->
    let l = List.map (conv_term ctx) l in
    [Stmt.Stmt_get_value l]
  | PA.Stmt_get_assertions
  | PA.Stmt_get_option _
  | PA.Stmt_get_info _
  | PA.Stmt_get_proof
  | PA.Stmt_get_unsat_core
  | PA.Stmt_get_unsat_assumptions
  | PA.Stmt_get_assignment
  | PA.Stmt_reset
  | PA.Stmt_reset_assertions
  | PA.Stmt_push _
  | PA.Stmt_pop _
    ->
    (* TODO: handle more of these *)
    errorf_ctx ctx "cannot handle statement %a" PA.pp_stmt stmt

