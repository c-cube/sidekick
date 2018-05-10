
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Loc = Locations
module Fmt = CCFormat

module A = Sidekick_smt.Ast
module PA = Parse_ast

type 'a or_error = ('a, string) CCResult.t

let pp_loc_opt = Loc.pp_opt

(** {2 Parsing} *)

module StrTbl = CCHashtbl.Make(struct
    type t = string
    let equal = CCString.equal
    let hash = CCString.hash
  end)

module Ctx = struct
  type kind =
    | K_ty of ty_kind
    | K_fun of A.Ty.t
    | K_var of A.var (* local *)
    | K_cstor of A.Ty.t
    | K_select of A.Ty.t * A.select

  and ty_kind =
    | K_uninterpreted (* uninterpreted type *)
    | K_other
    | K_bool
    | K_data (* data type *)

  type t = {
    names: ID.t StrTbl.t;
    kinds: kind ID.Tbl.t;
    data: (ID.t * A.Ty.t) list ID.Tbl.t; (* data -> cstors *)
    mutable loc: Loc.t option; (* current loc *)
  }

  let create () : t = {
    names=StrTbl.create 64;
    kinds=ID.Tbl.create 64;
    data=ID.Tbl.create 64;
    loc=None;
  }

  let loc t = t.loc
  let set_loc ?loc t = t.loc <- loc

  let add_id t (s:string) (k:kind): ID.t =
    let id = ID.make s in
    StrTbl.add t.names s id;
    ID.Tbl.add t.kinds id k;
    id

  let add_data t (id:ID.t) cstors: unit =
    ID.Tbl.add t.data id cstors

  let with_var t (s:string) (ty:A.Ty.t) (f:A.var -> 'a): 'a =
    let id = ID.make s in
    StrTbl.add t.names s id;
    let v = A.Var.make id ty in
    ID.Tbl.add t.kinds id (K_var v);
    CCFun.finally1 f v
      ~h:(fun () -> StrTbl.remove t.names s)

  let with_vars t (l:(string*A.Ty.t) list) (f:A.var list -> 'a): 'a =
    let rec aux ids l f = match l with
      | [] -> f (List.rev ids)
      | (s,ty) :: l' -> with_var t s ty (fun id -> aux (id::ids) l' f)
    in
    aux [] l f

  let find_kind t (id:ID.t) : kind =
    try ID.Tbl.find t.kinds id
    with Not_found -> Util.errorf "did not find kind of ID `%a`" ID.pp id

  let as_data t (ty:A.Ty.t) : (ID.t * A.Ty.t) list = match ty with
    | A.Ty.App (id,_) ->
      begin match ID.Tbl.get t.data id with
        | Some l -> l
        | None -> Util.errorf "expected %a to be a datatype" A.Ty.pp ty
      end
    | _ -> Util.errorf "expected %a to be a constant type" A.Ty.pp ty

  let pp_kind out = function
    | K_ty _ -> Format.fprintf out "type"
    | K_cstor ty ->
      Format.fprintf out "(@[cstor : %a@])" A.Ty.pp ty
    | K_select (ty,s) ->
      Format.fprintf out "(@[select-%a-%d : %a@])"
        ID.pp s.A.select_cstor s.A.select_i A.Ty.pp ty
    | K_fun ty ->
      Format.fprintf out "(@[fun : %a@])" A.Ty.pp ty
    | K_var v ->
      Format.fprintf out "(@[var : %a@])" A.Ty.pp (A.Var.ty v)

  let pp out t =
    Format.fprintf out "ctx {@[%a@]}"
      Fmt.(seq ~sep:(return "@ ") @@ pair ID.pp pp_kind) (ID.Tbl.to_seq t.kinds)
end

let error_loc ctx : string = Fmt.sprintf "at %a: " pp_loc_opt (Ctx.loc ctx)
let errorf_ctx ctx msg =
  Util.errorf ("at %a:@ " ^^ msg) pp_loc_opt (Ctx.loc ctx)

let check_bool_ t =
  if not (A.Ty.equal (A.ty t) A.Ty.prop) then (
    A.Ty.ill_typed "expected bool, got `@[%a : %a@]`" A.pp_term t A.Ty.pp (A.ty t)
  )

let find_id_ ctx (s:string): ID.t =
  try StrTbl.find ctx.Ctx.names s
  with Not_found -> errorf_ctx ctx "name `%s` not in scope" s

(* parse a type *)
let rec conv_ty ctx (t:PA.ty) : A.Ty.t * _ = match t with
  | PA.Ty_bool -> A.Ty.prop, Ctx.K_ty Ctx.K_bool
  | PA.Ty_app ("Rat",[]) -> A.Ty.rat, Ctx.K_ty Ctx.K_other
  | PA.Ty_app ("Int",[]) -> A.Ty.int , Ctx.K_ty Ctx.K_other
  | PA.Ty_app (f, l) ->
    let id = find_id_ ctx f in
    let l = List.map (conv_ty_fst ctx) l in
    A.Ty.app id l, Ctx.find_kind ctx id
  | PA.Ty_arrow (args, ret) ->
    let args = List.map (conv_ty_fst ctx) args in
    let ret, _ = conv_ty ctx ret in
    A.Ty.arrow_l args ret, Ctx.K_ty Ctx.K_other

and conv_ty_fst ctx t = fst (conv_ty ctx t)

let conv_var ctx (v,ty) = v, conv_ty_fst ctx ty
let conv_vars ctx l = List.map (fun (v,ty) -> v, conv_ty_fst ctx ty) l

let is_num s =
  let is_digit_or_dot = function '0' .. '9' | '.' -> true | _ -> false in
  if s.[0] = '-'
  then CCString.for_all is_digit_or_dot (String.sub s 1 (String.length s-1))
  else CCString.for_all is_digit_or_dot s

let rec conv_term ctx (t:PA.term) : A.term = match t with
  | PA.True -> A.true_
  | PA.False -> A.false_
  | PA.Const s when is_num s -> A.num_str A.Ty.rat s (* numeral *)
  | PA.Const f ->
    let id = find_id_ ctx f in
    begin match Ctx.find_kind ctx id with
      | Ctx.K_var v -> A.var v
      | Ctx.K_fun ty -> A.const id ty
      | Ctx.K_ty _ ->
        errorf_ctx ctx "expected term, not type; got `%a`" ID.pp id
      | Ctx.K_cstor ty -> A.const id ty
      | Ctx.K_select _ -> errorf_ctx ctx "unapplied `select` not supported"
    end
  | PA.If (a,b,c) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    A.if_ a b c
  | PA.Fun (v, body) ->
    let v = conv_var ctx v in
    Ctx.with_var ctx (fst v)(snd v)
      (fun v ->
         let body = conv_term ctx body in
         A.fun_ v body)
  | PA.Forall _ | PA.Exists _ ->
    errorf_ctx ctx "cannot process quantifiers in %a" PA.pp_term t
  | PA.Let (vbs, u) ->
    let vars, terms =
      List.map
        (fun (v,t) ->
           let t = conv_term ctx t in
           (v,A.ty t), t)
        vbs
      |> List.split
    in
    Ctx.with_vars ctx vars
      (fun vars ->
         let vbs = List.combine vars terms in
         let u = conv_term ctx u in
         A.let_l vbs u)
  | PA.Distinct l ->
    let l = List.map (conv_term ctx) l in
    A.op A.Distinct l
  | PA.And l ->
    let l = List.map (conv_term ctx) l in
    A.and_l l
  | PA.Or l ->
    let l = List.map (conv_term ctx) l in
    A.or_l l
  | PA.Not a ->
    let a = conv_term ctx a in
    A.not_ a
  | PA.Eq (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    A.eq a b
  | PA.Imply (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    A.imply a b
  | PA.Xor (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    A.or_ (A.and_ a (A.not_ b)) (A.and_ (A.not_ a) b)
  | PA.Match (lhs, l) ->
    (*
    errorf_ctx ctx "TODO: support match in %a" PA.pp_term t
    assert false
       *)
    (* convert a regular case *)
    let conv_case c vars rhs =
      let c_id = find_id_ ctx c in
      (* obtain the type *)
      let ty_args, _ty_ret = match Ctx.find_kind ctx c_id with
       | Ctx.K_cstor ty -> A.Ty.unfold ty
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
             let args, _ = A.Ty.unfold ty_cstor in
             let vars = List.mapi (fun i ty -> A.Var.makef ~ty "_%d" i) args in
             ID.Map.add cstor (vars, def_rhs) cases
           ))
        cases all_cstors
     in
     A.match_ lhs cases
  | PA.Arith (op, l) ->
    let l = List.map (conv_term ctx) l in
    List.iter
      (fun t ->
         if not (A.Ty.equal A.Ty.rat (A.ty t)) then (
           errorf_ctx ctx "expected rational term,@ got `%a`" A.pp_term t
         ))
      l;
    let ty, op = match op with
      | PA.Leq -> A.Ty.prop, A.Leq
      | PA.Lt -> A.Ty.prop,A. Lt
      | PA.Geq -> A.Ty.prop, A.Geq
      | PA.Gt -> A.Ty.prop, A.Gt
      | PA.Add -> A.Ty.rat, A.Add
      | PA.Minus -> A.Ty.rat, A.Minus
      | PA.Mult -> A.Ty.rat, A.Mult
      | PA.Div -> A.Ty.rat, A.Div
    in
    A.arith ty op l
  | PA.Cast (t, ty_expect) ->
    let t = conv_term ctx t in
    let ty_expect = conv_ty_fst ctx ty_expect in
    if not (A.Ty.equal (A.ty t) ty_expect) then (
      A.Ty.ill_typed "term `%a`@ should have type `%a`" A.pp_term t A.Ty.pp ty_expect
    );
    t
  | _ ->
    errorf_ctx ctx "unsupported term %a" PA.pp_term t

let find_file_ name ~dir : string option =
  Sidekick_sat.Log.debugf 2 (fun k->k "search %s in %s" name dir);
  let abs_path = Filename.concat dir name in
  if Sys.file_exists abs_path
  then Some abs_path
  else None

let conv_fun_decl ctx f : string * A.Ty.t =
  if f.PA.fun_ty_vars <> [] then (
    errorf_ctx ctx "cannot convert polymorphic function@ %a"
      (PA.pp_fun_decl PA.pp_ty) f
  );
  let args = List.map (conv_ty_fst ctx) f.PA.fun_args in
  let ty = A.Ty.arrow_l args (conv_ty_fst ctx f.PA.fun_ret) in
  f.PA.fun_name, ty

let conv_fun_def ctx f_decl body : string * A.Ty.t * (unit -> A.term) =
  if f_decl.PA.fun_ty_vars <> [] then (
    errorf_ctx ctx "cannot convert polymorphic function@ %a"
      (PA.pp_fun_decl PA.pp_typed_var) f_decl;
  );
  let args = conv_vars ctx f_decl.PA.fun_args in
  let ty =
    A.Ty.arrow_l
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

let rec conv_statement ctx (s:PA.statement): A.statement list =
  Log.debugf 4 (fun k->k "(@[<1>statement_of_ast@ %a@])" PA.pp_stmt s);
  Ctx.set_loc ctx ?loc:(PA.loc s);
  conv_statement_aux ctx s

and conv_statement_aux ctx (stmt:PA.statement) : A.statement list = match PA.view stmt with
  | PA.Stmt_set_logic s -> [A.SetLogic s]
  | PA.Stmt_set_option l -> [A.SetOption l]
  | PA.Stmt_set_info l -> [A.SetInfo l]
  | PA.Stmt_exit -> [A.Exit]
  | PA.Stmt_decl_sort (s,n) ->
    let id = Ctx.add_id ctx s (Ctx.K_ty Ctx.K_uninterpreted) in
    [A.TyDecl (id,n)]
  | PA.Stmt_decl fr ->
    let f, ty = conv_fun_decl ctx fr in
    let id = Ctx.add_id ctx f (Ctx.K_fun ty) in
    [A.Decl (id, ty)]
  | PA.Stmt_data ([],l) ->
    (* first, read and declare each datatype (it can occur in the other
    datatypes' construtors) *)
    let pre_parse (data_name,cases) =
      let data_id = Ctx.add_id ctx data_name (Ctx.K_ty Ctx.K_data) in
      data_id, cases
    in
    let l = List.map pre_parse l in
    (* now parse constructors *)
    let l =
     List.map
       (fun (data_id, (cstors:PA.cstor list)) ->
         let data_ty = A.Ty.const data_id in
         let parse_case {PA.cstor_name=c; cstor_args} =
           let selectors =
             List.map (fun (n,ty) -> Some n, conv_ty_fst ctx ty) cstor_args
           in
           let ty_args = List.map snd selectors in
           (* declare cstor *)
           let ty_c = A.Ty.arrow_l ty_args data_ty in
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
         {A.Ty.data_id; data_cstors=ID.Map.of_list cstors})
      l
    in
    [A.Data l]
  | PA.Stmt_data _ ->
    errorf_ctx ctx "not implemented: parametric datatypes" PA.pp_stmt stmt
  | PA.Stmt_funs_rec defs ->
    (* errorf_ctx ctx "not implemented: definitions" PA.pp_stmt stmt *)
    let {PA.fsr_decls=decls; fsr_bodies=bodies} = defs in
    if List.length decls <> List.length bodies then (
      errorf_ctx ctx "declarations and bodies should have same length";
    );
    let defs = conv_fun_defs ctx decls bodies in
    [A.Define defs]
  | PA.Stmt_fun_def
      {PA.fr_decl={PA.fun_ty_vars=[]; fun_args=[]; fun_name; fun_ret}; fr_body} ->
    (* turn [def f : ret := body] into [decl f : ret; assert f=body] *)
    let ret = conv_ty_fst ctx fun_ret in
    let id = Ctx.add_id ctx fun_name (Ctx.K_fun ret) in
    let rhs = conv_term ctx fr_body in
    [ A.Decl (id,ret);
      A.Assert (A.eq (A.const id ret) rhs);
    ]
  | PA.Stmt_fun_rec _
  | PA.Stmt_fun_def _
    -> errorf_ctx ctx "unsupported definition: %a" PA.pp_stmt stmt
  | PA.Stmt_assert t ->
    let t = conv_term ctx t in
    check_bool_ t;
    [A.Assert t]
  | PA.Stmt_assert_not ([], t) ->
    let vars, t = A.unfold_binder A.Forall (conv_term ctx t) in
    let g = A.not_ t in (* negate *)
    [A.Goal (vars, g)]
  | PA.Stmt_assert_not (_::_, _) ->
    errorf_ctx ctx "cannot convert polymorphic goal@ `@[%a@]`"
      PA.pp_stmt stmt
  | PA.Stmt_lemma _ ->
    errorf_ctx ctx "smbc does not know how to handle `lemma` statements"
  | PA.Stmt_check_sat -> [A.CheckSat]

