
(** {2 Conversion into {!Term.t}} *)

open Sidekick_smt

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module A = Ast
module Form = Sidekick_th_bool
module Fmt = CCFormat
module Dot = Msat_backend.Dot.Make(Solver.Sat_solver)(Msat_backend.Dot.Default(Solver.Sat_solver))

module Subst = struct
  type 'a t = 'a ID.Map.t
  let empty = ID.Map.empty
  let mem subst v = ID.Map.mem (A.Var.id v) subst
  let pp pp_x out = ID.Map.pp ~arrow:"→" ID.pp pp_x out
  let add subst v t =
    if mem subst v then (
      Error.errorf "%a already bound" A.Var.pp v;
    );
    ID.Map.add (A.Var.id v) t subst
  let find subst v = ID.Map.get (A.Var.id v) subst
  let find_exn subst v = ID.Map.find (A.Var.id v) subst
end

module Conv = struct
  let conv_ty (ty:A.Ty.t) : Ty.t =
    let mk_ty id = Ty.atomic_uninterpreted id in
    (* convert a type *)
    let aux_ty (ty:A.Ty.t) : Ty.t = match ty with
      | A.Ty.Prop -> Ty.prop
  (*     | A.Ty.Rat -> Reg.find_exn reg Mc2_lra.k_rat *)
      | A.Ty.App (id, []) -> mk_ty id
      | A.Ty.App (_, _) ->
        Error.errorf "cannot convert parametrized type %a" A.Ty.pp ty
      | A.Ty.Arrow _ ->
        Error.errorf "cannot convert arrow type `%a`" A.Ty.pp ty
    in
    aux_ty ty

  let conv_fun_ty (ty:A.Ty.t) : Ty.Fun.t =
    let rec aux args ty =
      match ty with
      | A.Ty.Arrow (a,b) ->
        aux (conv_ty a :: args) b
      | _ -> Ty.Fun.mk (List.rev args) (conv_ty ty)
    in
    aux [] ty

  let conv_term (tst:Term.state) (t:A.term): Term.t =
    (* polymorphic equality *)
    let mk_eq t u = Form.eq tst t u in (* TODO: use theory of booleans *)
    let mk_app f l = Term.app_cst tst f (IArray.of_list l) in
    let mk_const = Term.const tst in
    (*
    let mk_lra_pred = Reg.find_exn reg Mc2_lra.k_make_pred in
    let mk_lra_eq t u = mk_lra_pred Mc2_lra.Eq0 (RLE.diff t u) |> Term.Bool.pa in
    let side_clauses : atom list list ref = ref [] in
    (* introduce intermediate variable for LRA sub-expression *)
    let mk_lra_expr (e:RLE.t): term = match RLE.as_const e, RLE.as_singleton e with
      | Some n, _ -> Reg.find_exn reg Mc2_lra.k_make_const n
      | None, Some (n,t) when Q.equal n Q.one -> t
      | _ ->
        let id = mk_lra_id() in
        Log.debugf 30
          (fun k->k"(@[smtlib.name_lra@ %a@ :as %a@])" RLE.pp e ID.pp id);
        decl id [] (Reg.find_exn reg Mc2_lra.k_rat);
        let t = mk_const id in
        side_clauses := [mk_lra_eq (RLE.singleton1 t) e] :: !side_clauses;
        t
    in
    (* adaptative equality *)
    let mk_eq_t_tf (t:term) (u:term_or_form) : F.t = match u with
      | F u -> F.equiv (F.atom (Term.Bool.pa t)) u
      | T u when Term.is_bool u ->
        F.equiv (F.atom (Term.Bool.pa t)) (F.atom (Term.Bool.pa u))
      | T u -> mk_eq t u |> F.atom
      | Rat u -> mk_lra_eq (RLE.singleton1 t) u |> F.atom
    and mk_eq_tf_tf (t:term_or_form) (u:term_or_form) = match t, u with
      | T t, T u -> mk_eq t u |> F.atom
      | T t, Rat u | Rat u, T t -> mk_lra_eq (RLE.singleton1 t) u |> F.atom
      | Rat t, Rat u -> mk_lra_eq t u |> F.atom
      | F t, F u -> F.equiv t u
      | _ -> assert false
    in
       *)
    (* convert term.
       @param subst used to expand let-bindings on the fly *)
    let rec aux (subst:Term.t Subst.t) (t:A.term) : Term.t =
      begin match A.term_view t with
        | A.Var v ->
          begin match Subst.find subst v with
            | None -> Error.errorf "variable %a not bound" A.Var.pp v
            | Some t -> t
          end
        | A.Const id ->
          let ty = conv_fun_ty @@ A.ty t in
          mk_const (Cst.mk_undef id ty)
        | A.App (f, l) ->
          let l = List.map (aux subst) l in
          begin match A.term_view f with
            | A.Const id ->
              (* TODO: lookup definition of [f] *)
              mk_app (Cst.mk_undef id (conv_fun_ty @@ A.ty f)) l
            | _ -> Error.errorf "cannot process HO application %a" A.pp_term t
          end
        | A.If (a,b,c) ->
          let a = aux subst a in
          let b = aux subst b in
          let c = aux subst c in
          Term.if_ tst a b c
        | A.Let (vbs,u) ->
          let subst =
            List.fold_left
              (fun s (v,t) -> Subst.add s v (aux subst t))
              subst vbs
          in
          aux subst u
        | A.Op (A.And, l) -> Form.and_l tst (List.map (aux subst) l)
        | A.Op (A.Or, l) -> Form.or_l tst (List.map (aux subst) l)
        | A.Op (A.Imply, l) ->
          let l = List.map (aux subst) l in
          begin match List.rev l with
            | [] -> Term.true_ tst
            | ret :: hyps ->
              Form.imply tst hyps ret
          end
        | A.Op (A.Eq, l) ->
          let l = List.map (aux subst) l in
          let rec curry_eq = function
            | [] | [_] -> assert false
            | [a;b] -> [mk_eq a b]
            | a :: b :: tail ->
              mk_eq a b :: curry_eq (b::tail)
          in
          Form.and_l tst (curry_eq l)
        | A.Op (A.Distinct, l) ->
          Form.distinct tst @@ List.map (aux subst) l
        | A.Not f -> Form.not_ tst (aux subst f)
        | A.Bool true -> Term.true_ tst
        | A.Bool false -> Term.false_ tst
        | A.Num_q _n -> assert false (* TODO Mc2_lra.LE.const n |> ret_rat *)
        | A.Num_z _n -> assert false (* TODO Mc2_lra.LE.const (Q.of_bigint n) |> ret_rat *)
        | A.Arith (_op, _l) ->
          assert false
          (* TODO
          let l = List.map (aux_rat subst) l in
          begin match op, l with
            | A.Minus, [a] -> RLE.neg a |> ret_rat
            | _, [] | _, [_] ->
              Error.errorf "ill-formed arith expr:@ %a@ (need ≥ 2 args)" A.pp_term t
            | A.Leq, [a;b] ->
              let e = RLE.diff a b in
              mk_lra_pred Mc2_lra.Leq0 e |> ret_any
            | A.Geq, [a;b] ->
              let e = RLE.diff b a in
              mk_lra_pred Mc2_lra.Leq0 e |> ret_any
            | A.Lt, [a;b] ->
              let e = RLE.diff a b in
              mk_lra_pred Mc2_lra.Lt0 e |> ret_any
            | A.Gt, [a;b] ->
              let e = RLE.diff b a in
              mk_lra_pred Mc2_lra.Lt0 e |> ret_any
            | (A.Leq | A.Lt | A.Geq | A.Gt), _ ->
              Error.errorf "ill-formed arith expr:@ %a@ (binary operator)" A.pp_term t
            | A.Add, _ ->
              let e = List.fold_left (fun n t -> RLE.add t n) RLE.empty l in
              mk_lra_expr e |> ret_t
            | A.Minus, a::tail ->
              let e =
                List.fold_left
                  (fun n t -> RLE.diff n t)
                  a tail
              in
              mk_lra_expr e |> ret_t
            | A.Mult, _::_::_ ->
              let coeffs, terms =
                CCList.partition_map
                  (fun t -> match RLE.as_const t with
                     | None -> `Right t
                     | Some c -> `Left c)
                  l
              in
              begin match coeffs, terms with
                | c::c_tail, [] ->
                  List.fold_right RLE.mult c_tail (RLE.const c) |> ret_rat
                | _, [t] ->
                  List.fold_right RLE.mult coeffs t |> ret_rat
                | _ ->
                  Error.errorf "non-linear expr:@ `%a`" A.pp_term t
              end
            | A.Div, (first::l) ->
              (* support t/a/b/c where only [t] is a rational *)
              let coeffs =
                List.map
                  (fun c -> match RLE.as_const c with
                     | None ->
                       Error.errorf "non-linear expr:@ `%a`" A.pp_term t
                     | Some c -> Q.inv c)
                  l
              in
              List.fold_right RLE.mult coeffs first |> ret_rat
          end
             *)
        | A.Select _ -> assert false (* TODO *)
        | A.Match _ -> assert false (* TODO *)
        | A.Bind _ -> assert false (* TODO *)
        | A.Undefined_value -> assert false (* TODO *)
        | A.Asserting _ -> assert false (* TODO *)
      end
    in
    aux Subst.empty t
end

let conv_ty = Conv.conv_ty
let conv_term = Conv.conv_term

(* check SMT model *)
let check_smt_model (solver:Solver.Sat_solver.t) (hyps:_ Vec.t) (m:Model.t) : unit =
  Log.debug 1 "(smt.check-smt-model)";
  let open Solver_types in
  let module S = Solver.Sat_solver in
  let check_atom (lit:Lit.t) : Msat.lbool =
    Log.debugf 5 (fun k->k "(@[smt.check-smt-model.atom@ %a@])" Lit.pp lit);
    let a = S.make_atom solver lit in
    let sat_value = S.eval_atom solver a in
    let t, sign = Lit.as_atom lit in
    begin match Model.eval m t with
      | Some (V_bool b) ->
        let b = if sign then b else not b in
        if (sat_value <> Msat.L_undefined) &&
           ((b && sat_value=Msat.L_false) || (not b && sat_value=Msat.L_true)) then (
          Error.errorf "(@[check-model.error@ :atom %a@ :model-val %B@ :sat-val %a@])"
            S.Atom.pp a b Msat.pp_lbool sat_value
        ) else (
          Log.debugf 5
            (fun k->k "(@[check-model@ :atom %a@ :model-val %B@ :sat-val %a@])"
                S.Atom.pp a b Msat.pp_lbool sat_value);
        )
      | Some v ->
        Error.errorf "(@[check-model.error@ :atom %a@ :non-bool-value %a@])"
          S.Atom.pp a Value.pp v
      | None ->
        if sat_value <> Msat.L_undefined then (
          Error.errorf "(@[check-model.error@ :atom %a@ :no-smt-value@ :sat-val %a@])"
            S.Atom.pp a Msat.pp_lbool sat_value
        );
    end;
    sat_value
  in
  let check_c c =
    let bs = List.map check_atom c in
    if List.for_all (function Msat.L_true -> false | _ -> true) bs then (
      Error.errorf "(@[check-model.error.none-true@ :clause %a@ :vals %a@])"
        (Fmt.Dump.list Lit.pp) c Fmt.(Dump.list @@ Msat.pp_lbool) bs
    );
  in
  Vec.iter check_c hyps

(* call the solver to check-sat *)
let solve
    ?gc:_
    ?restarts:_
    ?dot_proof
    ?(pp_model=false)
    ?(check=false)
    ?time:_ ?memory:_ ?progress:_
    ?hyps
    ~assumptions
    s : unit =
  let t1 = Sys.time() in
  let res =
    Solver.solve ~assumptions s
    (* ?gc ?restarts ?time ?memory ?progress *)
  in
  let t2 = Sys.time () in
  begin match res with
    | Solver.Sat m ->
      if pp_model then (
        Format.printf "(@[<hv1>model@ %a@])@." Model.pp  m
      );
      if check then (
        Solver.check_model s;
        CCOpt.iter (fun h -> check_smt_model (Solver.solver s) h m) hyps;
      );
      let t3 = Sys.time () -. t2 in
      Format.printf "Sat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    | Solver.Unsat p ->
      if check then (
        Solver.Proof.check p;
        begin match dot_proof with
          | None ->  ()
          | Some file ->
            CCIO.with_out file
              (fun oc ->
                 Log.debugf 1 (fun k->k "write proof into `%s`" file);
                 let fmt = Format.formatter_of_out_channel oc in
                 Dot.pp fmt p;
                 Format.pp_print_flush fmt (); flush oc)
        end
      );
      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    | Solver.Unknown reas ->
      Format.printf "Unknown (:reason %a)" Solver.pp_unknown reas
  end

(* NOTE: hack for testing with dimacs. Proper treatment should go into
   scoping in Ast, or having theory-specific state in `Term.state` *)
let mk_iatom =
  let tbl = Util.Int_tbl.create 6 in (* for atoms *)
  fun tst i ->
    let c = Util.Int_tbl.get_or_add tbl ~k:(abs i) 
        ~f:(fun i -> Cst.mk_undef_const (ID.makef "a_%d" i) Ty.prop) in
    Lit.atom ~sign:(i>0) @@ Term.const tst c

(* process a single statement *)
let process_stmt
    ?hyps
    ?gc ?restarts ?(pp_cnf=false) ?dot_proof ?pp_model ?check
    ?time ?memory ?progress
    (solver:Solver.t)
    (stmt:Ast.statement) : unit or_error =
  Log.debugf 5
    (fun k->k "(@[<2>process statement@ %a@])" A.pp_statement stmt);
  let tst = Solver.tst solver in
  let decl_sort c n : unit =
    Log.debugf 1 (fun k->k "(@[declare-sort %a@ :arity %d@])" ID.pp c n);
    (* TODO: more? *)
  in
  let decl_fun id args ret : unit =
    Log.debugf 1
      (fun k->k "(@[declare-fun %a@ :args (@[%a@])@ :ret %a@])"
          ID.pp id (Util.pp_list Ty.pp) args Ty.pp ret);
    (* TODO: more? *)
  in
  begin match stmt with
    | A.SetLogic ("QF_UF"|"QF_LRA"|"QF_UFLRA") -> E.return ()
    | A.SetLogic s ->
      Log.debugf 0 (fun k->k "warning: unknown logic `%s`" s);
      E.return ()
    | A.SetOption l ->
      Log.debugf 0 (fun k->k "warning: unknown option `%a`" (Util.pp_list Fmt.string) l);
      E.return ()
    | A.SetInfo _ -> E.return ()
    | A.Exit ->
      Log.debug 1 "exit";
      raise Exit
    | A.CheckSat ->
      solve
        ?gc ?restarts ?dot_proof ?check ?pp_model ?time ?memory ?progress
        ~assumptions:[] ?hyps
        solver;
      E.return()
    | A.TyDecl (id,n) ->
      decl_sort id n;
      E.return ()
    | A.Decl (f,ty) ->
      let ty_args, ty_ret = A.Ty.unfold ty in
      let ty_args = List.map conv_ty ty_args in
      let ty_ret = conv_ty ty_ret in
      decl_fun f ty_args ty_ret;
      E.return ()
    | A.Assert t ->
      let t = conv_term tst t in
      if pp_cnf then (
        Format.printf "(@[<hv1>assert@ %a@])@." Term.pp t
      );
      let atom = Lit.atom t in
      CCOpt.iter (fun h -> Vec.push h [atom]) hyps;
      Solver.assume solver (IArray.singleton atom);
      E.return()
    | A.Assert_bool l ->
      let c = List.rev_map (mk_iatom tst) l in
      CCOpt.iter (fun h -> Vec.push h c) hyps;
      Solver.assume solver (IArray.of_list c);
      E.return ()
    | A.Goal (_, _) ->
      Error.errorf "cannot deal with goals yet"
    | A.Data _ ->
      Error.errorf "cannot deal with datatypes yet"
    | A.Define _ ->
      Error.errorf "cannot deal with definitions yet"
  end



(* FIXME: merge this
module Conv : sig
  val add_statement : Ast.statement -> unit
  val add_statement_l : Ast.statement list -> unit
  val ty_to_ast: Ty.t -> Ast.Ty.t
  val term_to_ast: term -> Ast.term
end = struct
  (* for converting Ast.Ty into Ty *)
  let ty_tbl_ : Ty.t lazy_t ID.Tbl.t = ID.Tbl.create 16

  (* for converting constants *)
  let decl_ty_ : cst lazy_t ID.Tbl.t = ID.Tbl.create 16

  (* environment for variables *)
  type conv_env = {
    let_bound: (term * int) ID.Map.t;
    (* let-bound variables, to be replaced. int=depth at binding position *)
    bound: (int * Ty.t) ID.Map.t;
    (* set of bound variables. int=depth at binding position *)
    depth: int;
  }

  let empty_env : conv_env =
    {let_bound=ID.Map.empty; bound=ID.Map.empty; depth=0}

  let rec conv_ty (ty:Ast.Ty.t): Ty.t = match ty with
    | Ast.Ty.Prop -> Ty.prop
    | Ast.Ty.Const id ->
      begin try ID.Tbl.find ty_tbl_ id |> Lazy.force
        with Not_found -> Error.errorf "type %a not in ty_tbl" ID.pp id
      end
    | Ast.Ty.Arrow (a,b) -> Ty.arrow (conv_ty a) (conv_ty b)

  let add_bound env v =
    let ty = Ast.Var.ty v |> conv_ty in
    { env with
        depth=env.depth+1;
        bound=ID.Map.add (Ast.Var.id v) (env.depth,ty) env.bound; }

  (* add [v := t] to bindings. Depth is not incremented
     (there will be no binders) *)
  let add_let_bound env v t =
    { env with
        let_bound=ID.Map.add (Ast.Var.id v) (t,env.depth) env.let_bound }

  let find_env env v =
    let id = Ast.Var.id v in
    ID.Map.get id env.let_bound, ID.Map.get id env.bound

  let rec conv_term_rec
      (env: conv_env)
      (t:Ast.term): term = match Ast.term_view t with
    | Ast.Bool true -> Term.true_
    | Ast.Bool false -> Term.false_
    | Ast.Unknown _ -> assert false
    | Ast.Const id ->
      begin
        try ID.Tbl.find decl_ty_ id |> Lazy.force |> Term.const
        with Not_found ->
          errorf "could not find constant `%a`" ID.pp id
      end
    | Ast.App (f, l) ->
      begin match Ast.term_view f with
        | Ast.Const id ->
          let f =
            try ID.Tbl.find decl_ty_ id |> Lazy.force
            with Not_found ->
              errorf "could not find constant `%a`" ID.pp id
          in
          let l = List.map (conv_term_rec env) l in
          if List.length l = fst (Ty.unfold_n (Cst.ty f))
          then Term.app_cst f (IArray.of_list l) (* fully applied *)
          else Term.app (Term.const f) l
        | _ ->
          let f = conv_term_rec env f in
          let l = List.map (conv_term_rec env) l in
          Term.app f l
      end
    | Ast.Var v ->
      (* look whether [v] must be replaced by some term *)
      begin match AstVarMap.get v env.subst with
        | Some t -> t
        | None ->
          (* lookup as bound variable *)
          begin match CCList.find_idx (Ast.Var.equal v) env.bound with
            | None -> errorf "could not find var `%a`" Ast.Var.pp v
            | Some (i,_) ->
              let ty = Ast.Var.ty v |> conv_ty in
              Term.db (DB.make i ty)
          end
      end
    | Ast.Bind (Ast.Fun,v,body) ->
      let body = conv_term_rec {env with bound=v::env.bound} body in
      let ty = Ast.Var.ty v |> conv_ty in
      Term.fun_ ty body
    | Ast.Bind ((Ast.Forall | Ast.Exists),_, _) ->
      errorf "quantifiers not supported"
    | Ast.Bind (Ast.Mu,v,body) ->
      let env' = add_bound env v in
      let body = conv_term_rec env' body in
      Term.mu body
    | Ast.Select _ -> assert false (* TODO *)
    | Ast.Match (u,m) ->
      let any_rhs_depends_vars = ref false in (* some RHS depends on matched arg? *)
      let m =
        ID.Map.map
          (fun (vars,rhs) ->
             let n_vars = List.length vars in
             let env', tys =
               CCList.fold_map
                 (fun env v -> add_bound env v, Ast.Var.ty v |> conv_ty)
                 env vars
             in
             let rhs = conv_term_rec env' rhs in
             let depends_on_vars =
               Term.to_seq_depth rhs
               |> Sequence.exists
                 (fun (t,k) -> match t.term_cell with
                    | DB db ->
                      DB.level db < n_vars + k (* [k]: number of intermediate binders *)
                    | _ -> false)
             in
             if depends_on_vars then any_rhs_depends_vars := true;
             tys, rhs)
          m
      in
      (* optim: check whether all branches return the same term, that
         does not depend on matched variables *)
      (* TODO: do the closedness check during conversion, above *)
      let rhs_l =
        ID.Map.values m
        |> Sequence.map snd
        |> Sequence.sort_uniq ~cmp:Term.compare
        |> Sequence.to_rev_list
      in
      begin match rhs_l with
        | [x] when not (!any_rhs_depends_vars) ->
          (* every branch yields the same [x], which does not depend
             on the argument: remove the match and return [x] instead *)
          x
        | _ ->
          let u = conv_term_rec env u in
          Term.match_ u m
      end
    | Ast.Switch _ ->
      errorf "cannot convert switch %a" Ast.pp_term t
    | Ast.Let (v,t,u) ->
      (* substitute on the fly *)
      let t = conv_term_rec env t in
      let env' = add_let_bound env v t in
      conv_term_rec env' u
    | Ast.If (a,b,c) ->
      let b = conv_term_rec env b in
      let c = conv_term_rec env c in
      (* optim: [if _ b b --> b] *)
      if Term.equal b c
      then b
      else Term.if_ (conv_term_rec env a) b c
    | Ast.Not t -> Term.not_ (conv_term_rec env t)
    | Ast.Binop (op,a,b) ->
      let a = conv_term_rec env a in
      let b = conv_term_rec env b in
      begin match op with
        | Ast.And -> Term.and_ a b
        | Ast.Or -> Term.or_ a b
        | Ast.Imply -> Term.imply a b
        | Ast.Eq -> Term.eq a b
      end
    | Ast.Undefined_value ->
      Term.undefined_value (conv_ty t.Ast.ty) Undef_absolute
    | Ast.Asserting (t, g) ->
      (* [t asserting g] becomes [if g t fail] *)
      let t = conv_term_rec env t in
      let g = conv_term_rec env g in
      Term.if_ g t (Term.undefined_value t.term_ty Undef_absolute)

  let add_statement st =
    Log.debugf 2
      (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
    model_env_ := Ast.env_add_statement !model_env_ st;
    begin match st with
      | Ast.Assert t ->
        let t = conv_term_rec empty_env t in
        Top_goals.push t;
        push_clause (Clause.make [Lit.atom t])
      | Ast.Goal (vars, t) ->
        (* skolemize *)
        let env, consts =
          CCList.fold_map
            (fun env v ->
               let ty = Ast.Var.ty v |> conv_ty in
               let c = Cst.make_undef (Ast.Var.id v) ty in
               {env with subst=AstVarMap.add v (Term.const c) env.subst}, c)
            empty_env
            vars
        in
        (* model should contain values of [consts] *)
        List.iter add_cst_support_ consts;
        let t = conv_term_rec env t in
        Top_goals.push t;
        push_clause (Clause.make [Lit.atom t])
      | Ast.TyDecl id ->
        let ty = Ty.atomic id Uninterpreted ~card:(Lazy.from_val Infinite) in
        add_ty_support_ ty;
        ID.Tbl.add ty_tbl_ id (Lazy.from_val ty)
      | Ast.Decl (id, ty) ->
        assert (not (ID.Tbl.mem decl_ty_ id));
        let ty = conv_ty ty in
        let cst = Cst.make_undef id ty in
        add_cst_support_ cst; (* need it in model *)
        ID.Tbl.add decl_ty_ id (Lazy.from_val cst)
      | Ast.Data l ->
        (* the datatypes in [l]. Used for computing cardinalities *)
        let in_same_block : ID.Set.t =
          List.map (fun {Ast.Ty.data_id; _} -> data_id) l |> ID.Set.of_list
        in
        (* declare the type, and all the constructors *)
        List.iter
          (fun {Ast.Ty.data_id; data_cstors} ->
             let ty = lazy (
               let card_ : ty_card ref = ref Finite in
               let cstors = lazy (
                 data_cstors
                 |> ID.Map.map
                   (fun c ->
                      let c_id = c.Ast.Ty.cstor_id in
                      let ty_c = conv_ty c.Ast.Ty.cstor_ty in
                      let ty_args, ty_ret = Ty.unfold ty_c in
                      (* add cardinality of [c] to the cardinality of [data_id].
                         (product of cardinalities of args) *)
                      let cstor_card =
                        ty_args
                        |> List.map
                          (fun ty_arg -> match ty_arg.ty_cell with
                             | Atomic (id, _) when ID.Set.mem id in_same_block ->
                               Infinite
                             | _ -> Lazy.force ty_arg.ty_card)
                        |> Ty_card.product
                      in
                      card_ := Ty_card.( !card_ + cstor_card );
                      let rec cst = lazy (
                        Cst.make_cstor c_id ty_c cstor
                      ) and cstor = lazy (
                        let cstor_proj = lazy (
                          let n = ref 0 in
                          List.map2
                            (fun id ty_arg ->
                               let ty_proj = Ty.arrow ty_ret ty_arg in
                               let i = !n in
                               incr n;
                               Cst.make_proj id ty_proj cstor i)
                            c.Ast.Ty.cstor_proj ty_args
                          |> IArray.of_list
                        ) in
                        let cstor_test = lazy (
                          let ty_test = Ty.arrow ty_ret Ty.prop in
                          Cst.make_tester c.Ast.Ty.cstor_test ty_test cstor
                        ) in
                        { cstor_ty=ty_c; cstor_cst=Lazy.force cst;
                          cstor_args=IArray.of_list ty_args;
                          cstor_proj; cstor_test; cstor_card; }
                      ) in
                      ID.Tbl.add decl_ty_ c_id cst; (* declare *)
                      Lazy.force cstor)
               )
               in
               let data = { data_cstors=cstors; } in
               let card = lazy (
                 ignore (Lazy.force cstors);
                 let r = !card_ in
                 Log.debugf 5
                   (fun k->k "(@[card_of@ %a@ %a@])" ID.pp data_id Ty_card.pp r);
                 r
               ) in
               Ty.atomic data_id (Data data) ~card
             ) in
             ID.Tbl.add ty_tbl_ data_id ty;
          )
          l;
        (* force evaluation *)
        List.iter
          (fun {Ast.Ty.data_id; _} ->
             let lazy ty = ID.Tbl.find ty_tbl_ data_id in
             ignore (Lazy.force ty.ty_card);
             begin match ty.ty_cell with
               | Atomic (_, Data {data_cstors=lazy _; _}) -> ()
               | _ -> assert false
             end)
          l
      | Ast.Define (k,l) ->
        (* declare the mutually recursive functions *)
        List.iter
          (fun (id,ty,rhs) ->
             let ty = conv_ty ty in
             let rhs = lazy (conv_term_rec empty_env rhs) in
             let k = match k with
               | Ast.Recursive -> Cst_recursive
               | Ast.Non_recursive -> Cst_non_recursive
             in
             let cst = lazy (
               Cst.make_defined id ty rhs k
             ) in
             ID.Tbl.add decl_ty_ id cst)
          l;
        (* force thunks *)
        List.iter
          (fun (id,_,_) -> ignore (ID.Tbl.find decl_ty_ id |> Lazy.force))
          l
    end

  let add_statement_l = List.iter add_statement

  module A = Ast

  let rec ty_to_ast (t:Ty.t): A.Ty.t = match t.ty_cell with
    | Prop -> A.Ty.Prop
    | Atomic (id,_) -> A.Ty.const id
    | Arrow (a,b) -> A.Ty.arrow (ty_to_ast a) (ty_to_ast b)

  let fresh_var =
    let n = ref 0 in
    fun ty ->
      let id = ID.makef "x%d" !n in
      incr n;
      A.Var.make id (ty_to_ast ty)

  let with_var ty env ~f =
    let v = fresh_var ty in
    let env = DB_env.push (A.var v) env in
    f v env

  let term_to_ast (t:term): Ast.term =
    let rec aux env t = match t.term_cell with
      | True -> A.true_
      | False -> A.false_
      | DB d ->
        begin match DB_env.get d env with
          | Some t' -> t'
          | None -> errorf "cannot find DB %a in env" Term.pp t
        end
      | App_cst (f, args) when IArray.is_empty args ->
        A.const f.cst_id (ty_to_ast t.term_ty)
      | App_cst (f, args) ->
        let f = A.const f.cst_id (ty_to_ast (Cst.ty f)) in
        let args = IArray.map (aux env) args in
        A.app f (IArray.to_list args)
      | App_ho (f,l) -> A.app (aux env f) (List.map (aux env) l)
      | Fun (ty,bod) ->
        with_var ty env
          ~f:(fun v env -> A.fun_ v (aux env bod))
      | Mu _ -> assert false
      | If (a,b,c) -> A.if_ (aux env a)(aux env b) (aux env c)
      | Case (u,m) ->
        let u = aux env u in
        let m =
          ID.Map.mapi
            (fun _c_id _rhs ->
               assert false  (* TODO: fetch cstor; bind variables; convert rhs *)
                 (*
               with_vars tys env ~f:(fun vars env -> vars, aux env rhs)
                    *)
            )
            m
        in
        A.match_ u m
      | Builtin b ->
        begin match b with
          | B_not t -> A.not_ (aux env t)
          | B_and (a,b) -> A.and_ (aux env a) (aux env b)
          | B_or (a,b) -> A.or_ (aux env a) (aux env b)
          | B_eq (a,b) -> A.eq (aux env a) (aux env b)
          | B_imply (a,b) -> A.imply (aux env a) (aux env b)
        end
    in aux DB_env.empty t
end
   *)
