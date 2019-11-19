(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Sidekick_base_term
module Loc = Smtlib_utils.V_2_6.Loc
module Fmt = CCFormat
module Log = Msat.Log

module PA = Smtlib_utils.V_2_6.Ast
module BT = Sidekick_base_term
module Ty = BT.Ty
module T = BT.Term
module Fun = BT.Fun
module Stmt = BT.Statement

type 'a or_error = ('a, string) CCResult.t

let pp_loc_opt = Loc.pp_opt

(** {2 Parsing} *)

module StrTbl = CCHashtbl.Make(CCString)

module Ctx = struct
  type kind =
    | K_ty of ty_kind
    | K_fun of Fun.t
    | K_cstor of Fun.t * Ty.t
    | K_select of Fun.t * Ty.t * BT.Select.t

  and ty_kind =
    | K_atomic of Ty.def
    | K_bool

  type t = {
    tst: T.state;
    names: ID.t StrTbl.t;
    kinds: kind ID.Tbl.t;
    lets: T.t StrTbl.t;
    data: (ID.t * Ty.t) list ID.Tbl.t; (* data -> cstors *)
    mutable loc: Loc.t option; (* current loc *)
  }

  let create (tst:T.state) : t = {
    tst;
    names=StrTbl.create 64;
    kinds=ID.Tbl.create 64;
    lets=StrTbl.create 16;
    data=ID.Tbl.create 64;
    loc=None;
  }

  let loc t = t.loc
  let set_loc ?loc t = t.loc <- loc

  let add_id_ self (s:string) (k:ID.t -> kind): ID.t =
    let id = ID.make s in
    StrTbl.add self.names s id;
    ID.Tbl.add self.kinds id (k id);
    id

  let add_id self (s:string) (k:kind): ID.t = add_id_ self s (fun _ ->k)

  let add_data self (id:ID.t) cstors: unit =
    ID.Tbl.add self.data id cstors

  (* locally bind [bs] and call [f], then remove bindings *)
  let with_lets (self:t) (bs:(string*T.t) list) (f:unit -> 'a): 'a =
    List.iter (fun (v,u) -> StrTbl.add self.lets v u) bs;
    CCFun.finally ~f
      ~h:(fun () ->
          List.iter (fun (v,_) -> StrTbl.remove self.lets v) bs)

  let find_kind self (id:ID.t) : kind =
    try ID.Tbl.find self.kinds id
    with Not_found -> Error.errorf "did not find kind of ID `%a`" ID.pp id

  let find_ty_def self (id:ID.t) : Ty.def =
    match find_kind self id with
    | K_ty (K_atomic def) -> def
    | _ -> Error.errorf "expected %a to be an atomic type" ID.pp id

  let as_data _self (ty:Ty.t) : BT.Data.t =
    match Ty.view ty with
    | Ty.Ty_atomic {def=Ty.Ty_data d;_} -> d
    | _ -> Error.errorf "expected %a to be a constant type" Ty.pp ty

  let pp_kind out = function
    | K_ty _ -> Format.fprintf out "type"
    | K_cstor (_,ty) ->
      Format.fprintf out "(@[cstor : %a@])" Ty.pp ty
    | K_select (_,ty,s) ->
      Format.fprintf out "(@[select-%a-%d : %a@])"
        ID.pp s.Select.select_cstor s.Select.select_i Ty.pp ty
    | K_fun f -> Fun.pp out f

  let pp out t =
    Format.fprintf out "ctx {@[%a@]}"
      Fmt.(seq ~sep:(return "@ ") @@ pair ID.pp pp_kind) (ID.Tbl.to_seq t.kinds)
end

let error_loc ctx : string = Fmt.sprintf "at %a: " pp_loc_opt (Ctx.loc ctx)
let errorf_ctx ctx msg =
  Error.errorf ("at %a:@ " ^^ msg) pp_loc_opt (Ctx.loc ctx)

let ill_typed ctx fmt =
  errorf_ctx ctx ("ill-typed: " ^^ fmt)

let check_bool_ ctx t =
  if not (Ty.equal (T.ty t) Ty.bool) then (
    ill_typed ctx "expected bool, got `@[%a : %a@]`" T.pp t Ty.pp (T.ty t)
  )

let find_id_ ctx (s:string): ID.t =
  try StrTbl.find ctx.Ctx.names s
  with Not_found -> errorf_ctx ctx "name `%s` not in scope" s

(* parse a type *)
let rec conv_ty ctx (t:PA.ty) : Ty.t = match t with
  | PA.Ty_bool -> Ty.bool
  | PA.Ty_real ->
    ill_typed ctx "cannot handle reals for now"
      (* FIXME
    Ty.rat, Ctx.K_ty Ctx.K_other
         *) 
  | PA.Ty_app ("Rat",[]) ->
    ill_typed ctx "cannot handle reals for now"
    (* TODO A.Ty.rat, Ctx.K_ty Ctx.K_other *)
  | PA.Ty_app ("Int",[]) ->
    ill_typed ctx "cannot handle ints for now"
    (* TODO: A.Ty.int , Ctx.K_ty Ctx.K_other *)
  | PA.Ty_app (f, l) ->
    let def = Ctx.find_ty_def ctx @@ find_id_ ctx f in
    let l = List.map (conv_ty ctx) l in
    Ty.atomic def l
  | PA.Ty_arrow _ ->
    ill_typed ctx "cannot handle arrow types"

let is_num s =
  let is_digit_or_dot = function '0' .. '9' | '.' -> true | _ -> false in
  if s.[0] = '-'
  then CCString.for_all is_digit_or_dot (String.sub s 1 (String.length s-1))
  else CCString.for_all is_digit_or_dot s

(* conversion of terms *)
let rec conv_term (ctx:Ctx.t) (t:PA.term) : T.t =
  let tst = ctx.Ctx.tst in
  match t with
  | PA.True -> T.true_ tst
  | PA.False -> T.false_ tst
  | PA.Const s when is_num s ->
    errorf_ctx ctx "cannot handle numbers for now"
    (* FIXME   A.num_str Ty.rat s (* numeral *) *)
  | PA.Const f
  | PA.App (f, []) ->
    (* lookup in `let` table, then in type defs *)
    begin match StrTbl.find ctx.Ctx.lets f with
      | u -> u
      | exception Not_found ->
        let id = find_id_ ctx f in
        begin match Ctx.find_kind ctx id with
          | Ctx.K_fun f -> T.const tst f
          | Ctx.K_ty _ ->
            errorf_ctx ctx "expected term, not type; got `%a`" ID.pp id
          | Ctx.K_cstor _ ->
            errorf_ctx ctx "cannot handle constructors for now"
            (* FIXME: A.const id ty *)
          | Ctx.K_select _ -> errorf_ctx ctx "unapplied `select` not supported"
        end
    end
  | PA.App (f, args) ->
    let id = find_id_ ctx f in
    let args = List.map (conv_term ctx) args in
    begin match Ctx.find_kind ctx id with
      | Ctx.K_fun f -> T.app_fun tst f (IArray.of_list args)
      | _ ->
        (* TODO: constructor + selector *)
        errorf_ctx ctx "expected constant application; got `%a`" ID.pp id
    end
  | PA.If (a,b,c) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    T.ite tst a b c
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
  | PA.Arith (_op, _l) ->
    errorf_ctx ctx "cannot handle arith construct %a" PA.pp_term t
      (* FIXME: arith
    let l = List.map (conv_term ctx) l in
    List.iter
      (fun t ->
         if not (Ty.equal Ty.rat (A.ty t)) then (
           errorf_ctx ctx "expected rational term,@ got `%a`" A.pp_term t
         ))
      l;
    let ty, op = match op with
      | PA.Leq -> Ty.prop, A.Leq
      | PA.Lt -> Ty.prop,A. Lt
      | PA.Geq -> Ty.prop, A.Geq
      | PA.Gt -> Ty.prop, A.Gt
      | PA.Add -> Ty.rat, A.Add
      | PA.Minus -> Ty.rat, A.Minus
      | PA.Mult -> Ty.rat, A.Mult
      | PA.Div -> Ty.rat, A.Div
    in
    A.arith ty op l
         *)
  | PA.Cast (t, ty_expect) ->
    let t = conv_term ctx t in
    let ty_expect = conv_ty ctx ty_expect in
    if not (Ty.equal (T.ty t) ty_expect) then (
      ill_typed ctx "term `%a`@ should have type `%a`" T.pp t Ty.pp ty_expect
    );
    t
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
    let id = Ctx.add_id_ ctx s
        (fun id -> Ctx.K_ty (Ctx.K_atomic (Ty.Ty_uninterpreted id))) in
    [Stmt.Stmt_ty_decl (id, n)]
  | PA.Stmt_decl fr ->
    let f, args, ret = conv_fun_decl ctx fr in
    let id = Ctx.add_id_ ctx f
        (fun id -> Ctx.K_fun (Fun.mk_undef' id args ret)) in
    [Stmt.Stmt_decl (id, args,ret)]
  | PA.Stmt_data l when List.for_all (fun ((_,n),_) -> n=0) l ->
    errorf_ctx ctx "cannot typecheck datatypes"
    (* FIXME
    (* first, read and declare each datatype (it can occur in the other
      datatypes' constructors) *)
    let pre_parse ((data_name,arity),cases) =
      if arity <> 0 then (
        errorf_ctx ctx "cannot handle polymorphic datatype %s" data_name;
      );
      let data_id = Ctx.add_id ctx data_name (Ctx.K_ty Ctx.K_data) in
      data_id, cases
    in
    let l = List.map pre_parse l in
    (* now parse constructors *)
    let l =
     List.map
       (fun (data_id, (cstors:PA.cstor list)) ->
         let data_ty = Ty.const data_id in
         let parse_case {PA.cstor_name=c; cstor_args; cstor_ty_vars} =
           if cstor_ty_vars <> [] then (
             errorf_ctx ctx "cannot handle polymorphic constructor %s" c;
           );
           let selectors =
             List.map (fun (n,ty) -> Some n, conv_ty_fst ctx ty) cstor_args
           in
           let ty_args = List.map snd selectors in
           (* declare cstor *)
           let ty_c = Ty.arrow_l ty_args data_ty in
           let id_c = Ctx.add_id ctx c (Ctx.K_cstor ty_c) in
           (* now declare selectors *)
           List.iteri
             (fun i (name_opt,ty) -> match name_opt with
                | None -> ()
                | Some select_str ->
                  (* declare this selector *)
                  let rec select_name = lazy
                    (Ctx.add_id ctx select_str
                       (Ctx.K_select (ty,
                          {A.select_name; select_cstor=id_c; select_i=i})))
                  in
                  ignore (Lazy.force select_name))
             selectors;
           (* return cstor *)
           id_c, ty_c
         in
         let cstors = List.map parse_case cstors in
         (* update info on [data] *)
         Ctx.add_data ctx data_id cstors;
         {Ty.data_id; data_cstors=ID.Map.of_list cstors})
      l
    in
    [A.Data l]
       *)
  | PA.Stmt_data _ ->
    errorf_ctx ctx "not implemented: parametric datatypes" PA.pp_stmt stmt
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
    let id = Ctx.add_id_ ctx fun_name
        (fun id -> Ctx.K_fun (Fun.mk_undef_const id ret)) in
    let f = match Ctx.find_kind ctx id with Ctx.K_fun f->f | _ -> assert false in
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
  | PA.Stmt_check_sat -> [Stmt.Stmt_check_sat]
  | PA.Stmt_check_sat_assuming _
  | PA.Stmt_get_assertions 
  | PA.Stmt_get_option _
  | PA.Stmt_get_info _
  | PA.Stmt_get_model
  | PA.Stmt_get_proof
  | PA.Stmt_get_unsat_core
  | PA.Stmt_get_unsat_assumptions
  | PA.Stmt_get_assignment
  | PA.Stmt_reset
  | PA.Stmt_reset_assertions
  | PA.Stmt_push _
  | PA.Stmt_pop _
  | PA.Stmt_get_value _
    ->
    (* TODO: handle more of these *)
    errorf_ctx ctx "cannot handle statement %a" PA.pp_stmt stmt

