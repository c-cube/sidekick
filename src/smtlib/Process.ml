(** {2 Conversion into {!Term.t}} *)

open Sidekick_base_term

[@@@ocaml.warning "-32"]

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module A = Ast
module Fmt = CCFormat

module Form =  struct
  module T = Term
  open Sidekick_th_bool_static
  exception Not_a_th_term

  let id_and = ID.make "and"
  let id_or = ID.make "or"
  let id_imply = ID.make "=>"
  let id_ite = ID.make "ite"

  let view_id fid args =
    if ID.equal fid id_and then (
      B_and args
    ) else if ID.equal fid id_or then (
      B_or args
    ) else if ID.equal fid id_imply && IArray.length args >= 2 then (
      (* conclusion is stored first *)
      let len = IArray.length args in
      B_imply (IArray.sub args 1 (len-1), IArray.get args 0)
    ) else if ID.equal fid id_ite && IArray.length args = 3 then (
      B_ite (IArray.get args 0, IArray.get args 1, IArray.get args 2)
    ) else (
      raise_notrace Not_a_th_term
    )

  let view_as_bool (t:T.t) : T.t bool_view =
    match T.view t with
    | Bool b -> B_bool b
    | Not u -> B_not u
    | Eq (a, b) when Ty.is_bool (T.ty a) -> B_equiv (a,b)
    | App_fun ({fun_id; _}, args) ->
      (try view_id fun_id args with Not_a_th_term -> B_atom t)
    | _ -> B_atom t

  module Funs = struct
    let get_ty id args =
      if ID.equal id id_ite then T.ty (IArray.get args 1)
      else Ty.bool

    let abs ~self _a =
      match T.view self with
      | Not u -> u, false
      | _ -> self, true

    (* no congruence closure for boolean terms *)
    let relevant _id _ _ = false

    let eval id args =
      let open Value in
      match view_id id args with
      | B_bool b -> Value.bool b
      | B_not (V_bool b) -> Value.bool (not b)
      | B_and a when IArray.for_all Value.is_true a -> Value.true_
      | B_and a when IArray.exists Value.is_false a -> Value.false_
      | B_or a when IArray.exists Value.is_true a -> Value.true_
      | B_or a when IArray.for_all Value.is_false a -> Value.false_
      | B_imply (_, V_bool true) -> Value.true_
      | B_imply (a,_) when IArray.exists Value.is_false a -> Value.true_
      | B_imply (a,b) when IArray.for_all Value.is_bool a && Value.is_bool b -> Value.false_
      | B_ite(a,b,c) ->
        if Value.is_true a then b
        else if Value.is_false a then c
        else Error.errorf "non boolean value %a in ite" Value.pp a
      | B_equiv (a,b) | B_eq(a,b) -> Value.bool (Value.equal a b)
      | B_atom v -> v
      | B_not _ | B_and _ | B_or _ | B_imply _
        -> Error.errorf "non boolean value in boolean connective"

    let mk_fun ?(do_cc=false) id : Fun.t =
      {fun_id=id;
       fun_view=Fun_def {
           pp=None; abs; ty=get_ty; relevant; do_cc; eval=eval id; }; }

    let and_ = mk_fun id_and
    let or_ = mk_fun id_or
    let imply = mk_fun id_imply
    let ite = mk_fun id_ite
  end

  let as_id id (t:T.t) : T.t IArray.t option =
    match T.view t with
    | App_fun ({fun_id; _}, args) when ID.equal id fun_id -> Some args
    | _ -> None

  (* flatten terms of the given ID *)
  let flatten_id op sign (l:T.t list) : T.t list =
    CCList.flat_map
      (fun t -> match as_id op t with
         | Some args -> IArray.to_list args
         | None when (sign && T.is_true t) || (not sign && T.is_false t) ->
           [] (* idempotent *)
         | None -> [t])
      l

  let and_l st l =
    match flatten_id id_and true l with
    | [] -> T.true_ st
    | l when List.exists T.is_false l -> T.false_ st
    | [x] -> x
    | args -> T.app_fun st Funs.and_ (IArray.of_list args)

  let or_l st l =
    match flatten_id id_or false l with
    | [] -> T.false_ st
    | l when List.exists T.is_true l -> T.true_ st
    | [x] -> x
    | args -> T.app_fun st Funs.or_ (IArray.of_list args)

  let and_ st a b = and_l st [a;b]
  let or_ st a b = or_l st [a;b]
  let and_a st a = and_l st (IArray.to_list a)
  let or_a st a = or_l st (IArray.to_list a)
  let eq = T.eq
  let not_ = T.not_

  let ite st a b c = match T.view a with
    | T.Bool ba -> if ba then b else c
    | _ -> T.app_fun st Funs.ite (IArray.of_array_unsafe [| a;b;c |])

  let equiv st a b =
    if T.equal a b then T.true_ st
    else if T.is_true a then b
    else if T.is_true b then a
    else if T.is_false a then not_ st b
    else if T.is_false b then not_ st a
    else T.eq st a b

  let neq st a b = not_ st @@ eq st a b

  let imply_a st xs y =
    if IArray.is_empty xs then y
    else T.app_fun st Funs.imply (IArray.append (IArray.singleton y) xs)

  let imply_l st xs y = match xs with
    | [] -> y
    | _ -> T.app_fun st Funs.imply (IArray.of_list @@ y :: xs)

  let imply st a b = imply_a st (IArray.singleton a) b

  let distinct_l tst l =
    match l with
    | [] | [_] -> T.true_ tst
    | l ->
      (* turn into [and_{i<j} t_i != t_j] *)
      let cs =
        CCList.diagonal l |> List.map (fun (a,b) -> neq tst a b) 
      in
      and_l tst cs

  let mk_bool st = function
    | B_bool b -> T.bool st b
    | B_atom t -> t
    | B_and l -> and_a st l
    | B_or l -> or_a st l
    | B_imply (a,b) -> imply_a st a b
    | B_ite (a,b,c) -> ite st a b c
    | B_equiv (a,b) -> equiv st a b
    | B_eq (a,b) -> T.eq st a b
    | B_not t -> not_ st t

  module Gensym = struct
    type t = {
      tst: T.state;
      mutable fresh: int;
    }

    let create tst : t = {tst; fresh=0}

    let fresh_term (self:t) ~pre (ty:Ty.t) : T.t =
      let name = Printf.sprintf "_tseitin_%s%d" pre self.fresh in
      self.fresh <- 1 + self.fresh;
      let id = ID.make name in
      T.const self.tst @@ Fun.mk_undef_const id ty
  end
end

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
      | A.Ty.Prop -> Ty.bool
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
    let mk_eq t u = Term.eq tst t u in
    let mk_app f l = Term.app_fun tst f (IArray.of_list l) in
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
          mk_const (Fun.mk_undef id ty)
        | A.App (f, l) ->
          let l = List.map (aux subst) l in
          begin match A.term_view f with
            | A.Const id ->
              (* TODO: lookup definition of [f] *)
              mk_app (Fun.mk_undef id (conv_fun_ty @@ A.ty f)) l
            | _ -> Error.errorf "cannot process HO application %a" A.pp_term t
          end
        | A.If (a,b,c) ->
          let a = aux subst a in
          let b = aux subst b in
          let c = aux subst c in
          Form.ite tst a b c
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
              Form.imply_l tst hyps ret
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
          Form.distinct_l tst @@ List.map (aux subst) l
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

(* instantiate solver here *)
module Solver_arg = struct
  include Sidekick_base_term

  let cc_view = Term.cc_view
  module Proof = struct
    type t = Default
    let default=Default
    let pp out _ = Fmt.string out "default"
  end
end
module Solver = Sidekick_msat_solver.Make(Solver_arg)

module Check_cc = struct
  module Lit = Solver.Solver_internal.Lit
  module SI = Solver.Solver_internal
  module CC = Solver.Solver_internal.CC
  module MCC = Sidekick_mini_cc.Make(Solver_arg)

  let pp_c out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∨ " Lit.pp) c
  let pp_and out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∧ " Lit.pp) c

  let add_cc_lit (cc:MCC.t) (lit:Lit.t) : unit =
    let t = Lit.term lit in
    MCC.add_lit cc t (Lit.sign lit)

  (* check that this is a proper CC conflict *)
  let check_conflict si _cc (confl:Lit.t list) : unit =
    Log.debugf 15 (fun k->k "(@[check-cc-conflict@ %a@])" pp_c confl);
    let tst = SI.tst si in
    let cc = MCC.create tst in
    (* add [¬confl] and check it's unsat *)
    List.iter (fun lit -> add_cc_lit cc @@ Lit.neg lit) confl;
    if MCC.check_sat cc then (
      Error.errorf "@[<2>check-cc-conflict:@ @[clause %a@]@ \
                    is not a UF tautology (negation is sat)@]" pp_c confl
    ) else (
      Log.debugf 15 (fun k->k "(@[check-cc-conflict.ok@ %a@])" pp_c confl);
    )

  let check_propagation si _cc p reason : unit =
    let reason = reason() in
    Log.debugf 15 (fun k->k "(@[check-cc-prop@ %a@ :reason %a@])" Lit.pp p pp_and reason);
    let tst = SI.tst si in
    let cc = MCC.create tst in
    (* add [reason & ¬lit] and check it's unsat *)
    List.iter (add_cc_lit cc) reason;
    add_cc_lit cc (Lit.neg p);
    if MCC.check_sat cc then (
      Error.errorf "@[<2>check-cc-prop:@ @[%a => %a@]@ \
                    is not a UF tautology (negation is sat)@]" pp_and reason Lit.pp p
    ) else (
      Log.debugf 15
        (fun k->k "(@[check-cc-prop.ok@ @[%a => %a@]@])" pp_and reason Lit.pp p);
    )


  let theory =
    Solver.mk_theory ~name:"cc-check"
      ~create_and_setup:(fun si ->
          Solver.Solver_internal.on_cc_conflict si (check_conflict si))
      ()

end

(* TODO
(* check SMT model *)
let check_smt_model (solver:Solver.Sat_solver.t) (hyps:_ Vec.t) (m:Model.t) : unit =
  Log.debug 1 "(smt.check-smt-model)";
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
   *)

let mk_progress () : _ -> unit =
  let start = Sys.time() in
  let n = ref 0 in
  let syms = "|\\-/" in
  fun _s ->
    let diff = Sys.time() -. start in
    incr n;
    (* limit frequency *)
    if float !n > 6. *. diff then (
      let sym = String.get syms (!n mod String.length syms) in
      Printf.printf "\r [%.2fs %c]" diff sym;
      n := 0;
      flush stdout
    )

(* call the solver to check-sat *)
let solve
    ?gc:_
    ?restarts:_
    ?dot_proof
    ?(pp_model=false)
    ?(check=false)
    ?time:_ ?memory:_ ?(progress=false)
    ?hyps:_
    ~assumptions
    s : unit =
  let t1 = Sys.time() in
  let on_progress =
    if progress then Some (mk_progress()) else None in
  let res =
    Solver.solve ~assumptions ?on_progress s
    (* ?gc ?restarts ?time ?memory ?progress *)
  in
  let t2 = Sys.time () in
  Printf.printf "\r"; flush stdout;
  begin match res with
    | Solver.Sat m ->
      if pp_model then (
        (* TODO: use actual {!Model} in the solver? or build it afterwards *)
        Format.printf "(@[<hv1>model@ %a@])@." Solver.Model.pp m
      );
      (* TODO
      if check then (
        Solver.check_model s;
        CCOpt.iter (fun h -> check_smt_model (Solver.solver s) h m) hyps;
      );
         *)
      let t3 = Sys.time () -. t2 in
      Format.printf "Sat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    | Solver.Unsat {proof=None;_} ->
      Format.printf "Unsat (%.3f/%.3f/-)@." t1 (t2-.t1);
    | Solver.Unsat {proof=Some p;_} ->
      if check then (
        Solver.Proof.check p;
      );
      begin match dot_proof with
        | None ->  ()
        | Some file ->
          CCIO.with_out file
            (fun oc ->
               Log.debugf 1 (fun k->k "write proof into `%s`" file);
               let fmt = Format.formatter_of_out_channel oc in
               Solver.Proof.pp_dot fmt p;
               Format.pp_print_flush fmt (); flush oc)
      end;
      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    | Solver.Unknown reas ->
      Format.printf "Unknown (:reason %a)" Solver.Unknown.pp reas
  end

(* process a single statement *)
let process_stmt
    ?hyps
    ?gc ?restarts ?(pp_cnf=false) ?dot_proof ?pp_model ?(check=false)
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
        ?gc ?restarts ?dot_proof ~check ?pp_model ?time ?memory ?progress
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
      let atom = Solver.mk_atom_t solver t in
      CCOpt.iter (fun h -> Vec.push h [atom]) hyps;
      Solver.add_clause solver (IArray.singleton atom);
      E.return()
    | A.Goal (_, _) ->
      Error.errorf "cannot deal with goals yet"
    | A.Data _ ->
      Error.errorf "cannot deal with datatypes yet"
    | A.Define _ ->
      Error.errorf "cannot deal with definitions yet"
  end

module Th_bool = Sidekick_th_bool_static.Make(struct
  module S = Solver
  type term = S.A.Term.t
  include Form
end)

let th_bool : Solver.theory =
  Th_bool.theory
