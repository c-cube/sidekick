
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

module A = Ast

type term = A.term
type ty = A.Ty.t
type domain = ID.t list

type t = {
  env: A.env;
  (* environment, defining symbols *)
  domains: domain A.Ty.Map.t;
  (* uninterpreted type -> its domain *)
  consts: term ID.Map.t;
  (* constant -> its value *)
}

let make ~env ~consts ~domains =
  (* also add domains to [env] *)
  let env =
    A.Ty.Map.to_seq domains
    |> Sequence.flat_map_l (fun (ty,l) -> List.map (CCPair.make ty) l)
    |> Sequence.fold
      (fun env (_,cst) -> A.env_add_def env cst A.E_uninterpreted_cst)
      env
  in
  {env; consts; domains}

type entry =
  | E_ty of ty * domain
  | E_const of ID.t * term

let pp out (m:t) =
  let pp_cst_name out c = ID.pp_name out c in
  let pp_ty = A.Ty.pp in
  let pp_term = A.pp_term in
  let pp_entry out = function
    | E_ty (ty,l) ->
      Format.fprintf out "(@[<1>type@ %a@ (@[<hv>%a@])@])"
        pp_ty ty (Util.pp_list pp_cst_name) l
    | E_const (c,t) ->
      Format.fprintf out "(@[<1>val@ %a@ %a@])"
        ID.pp_name c pp_term t
  in
  let es =
    CCList.append
      (A.Ty.Map.to_list m.domains |> List.map (fun (ty,dom) -> E_ty (ty,dom)))
      (ID.Map.to_list m.consts |> List.map (fun (c,t) -> E_const (c,t)))
  in
  Format.fprintf out "(@[<v>%a@])" (Util.pp_list pp_entry) es

exception Bad_model of t * term * term
exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("internal error: " ^ msg)
      | Bad_model (m,t,t') ->
        let msg = CCFormat.sprintf
            "@[<hv2>Bad model:@ goal `@[%a@]`@ evaluates to `@[%a@]`,@ \
             not true,@ in model @[%a@]@."
            A.pp_term t A.pp_term t' pp m
        in
        Some msg
      | _ -> None)

let errorf msg = CCFormat.ksprintf msg ~f:(fun s -> raise (Error s))

module VarMap = CCMap.Make(struct
    type t = A.Ty.t A.Var.t
    let compare = A.Var.compare
  end)

(* var -> term in normal form *)
type subst = A.term lazy_t VarMap.t

let empty_subst : subst = VarMap.empty

let rename_var subst v =
  let v' = A.Var.copy v in
  VarMap.add v (Lazy.from_val (A.var v')) subst, v'

let rename_vars = CCList.fold_map rename_var

let pp_subst out (s:subst) =
  let pp_pair out (v,lazy t) =
    Format.fprintf out "@[<2>%a@ @<1>→ %a@]" A.Var.pp v A.pp_term t
  in
  Format.fprintf out "[@[%a@]]"
    CCFormat.(list ~sep:(return ",@ ") pp_pair) (VarMap.to_list s |> List.rev)

let rec as_cstor_app env t = match A.term_view t with
  | A.Const id ->
    begin match A.env_find_def env id with
      | Some (A.E_cstor ty) -> Some (id, ty, [])
      | _ -> None
    end
  | A.App (f, l) ->
    CCOpt.map (fun (id,ty,l') -> id,ty,l'@l) (as_cstor_app env f)
  | _ -> None

let pp_stack out (l:term list) : unit =
  let ppt out t = Format.fprintf out "(@[%a@ :ty %a@])" A.pp_term t A.Ty.pp t.A.ty in
  CCFormat.(within "[" "]" (hvbox (list ppt))) out l

let apply_subst (subst:subst) t =
  let rec aux subst t = match A.term_view t with
    | A.Num_z _ | A.Num_q _ -> t
    | A.Var v ->
      begin match VarMap.get v subst with
        | None -> t
        | Some (lazy t') -> t'
      end
    | A.Undefined_value
    | A.Bool _ | A.Const _ -> t
    | A.Select (sel, t) -> A.select ~ty:t.A.ty sel (aux subst t)
    | A.App (f,l) -> A.app (aux subst f) (List.map (aux subst) l)
    | A.If (a,b,c) -> A.if_ (aux subst a) (aux subst b) (aux subst c)
    | A.Match (u,m) ->
      A.match_ (aux subst u)
        (ID.Map.map
           (fun (vars,rhs) ->
              let subst, vars = rename_vars subst vars in
              vars, aux subst rhs) m)
    | A.Let (vbs,u) ->
      let subst', vbs' =
        CCList.fold_map
          (fun subst' (x,t) ->
             let t = aux subst t in
             let subst', x' = rename_var subst' x in
             subst', (x',t))
          subst vbs
      in
      A.let_l vbs' (aux subst' u)
    | A.Bind (A.Mu, _,_) -> assert false
    | A.Bind (b, x,body) ->
      let subst', x'  = rename_var subst x in
      A.bind ~ty:(A.ty t) b x' (aux subst' body)
    | A.Not f -> A.not_ (aux subst f)
    | A.Op (op,l) -> A.op op (List.map (aux subst) l)
    | A.Asserting {t;guard} ->
      A.asserting (aux subst t) (aux subst guard)
    | A.Arith (op,l) ->
      let ty = A.ty t in
      A.arith ty op (List.map (aux subst) l)
  in
  if VarMap.is_empty subst then t else aux subst t

type partial_eq =
  | Eq
  | Neq
  | Unknown

let equal_as_values (_:A.term) (_:A.term) : partial_eq =
  Unknown (* TODO *)

(* Weak Head Normal Form.
   @param m the model
   @param st the "stack trace" (terms around currently being evaluated)
   @param t the term to eval *)
let rec eval_whnf (m:t) (st:term list) (subst:subst) (t:term): term =
  Sidekick_sat.Log.debugf 5
    (fun k->k "%s@[<2>eval_whnf `@[%a@]`@ in @[%a@]@]"
        (String.make (List.length st) ' ') (* indent *)
        A.pp_term t pp_subst subst);
  let st = t :: st in
  try
    eval_whnf_rec m st subst t
  with Util.Error msg ->
    errorf "@[<2>Model:@ internal type error `%s`@ in %a@]" msg pp_stack st
and eval_whnf_rec m st subst t = match A.term_view t with
  | A.Num_q _
  | A.Num_z _ -> t
  | A.Undefined_value | A.Bool _ -> t
  | A.Var v ->
    begin match VarMap.get v subst with
      | None -> t
      | Some (lazy t') ->
        eval_whnf m st empty_subst t'
    end
  | A.Const c ->
    begin match A.env_find_def m.env c with
      | Some (A.E_defined (_, t')) -> eval_whnf m st empty_subst t'
      | _ ->
        begin match ID.Map.get c m.consts with
          | None -> t
          | Some {A.term=A.Const c';_} when (ID.equal c c') -> t (* trivial cycle *)
          | Some t' -> eval_whnf m st empty_subst t'
        end
    end
  | A.App (f,l) -> eval_whnf_app m st subst subst f l
  | A.If (a,b,c) ->
    let a = eval_whnf m st subst a in
    begin match A.term_view a with
      | A.Bool true -> eval_whnf m st subst b
      | A.Bool false -> eval_whnf m st subst c
      | _ ->
        let b = apply_subst subst b in
        let c = apply_subst subst c in
        A.if_ a b c
    end
  | A.Bind (A.Mu,v,body) ->
    let subst' = VarMap.add v (lazy t) subst in
    eval_whnf m st subst' body
  | A.Let (vbs,u) ->
    let subst =
      List.fold_left
        (fun subst (x,t) ->
             let t = lazy (eval_whnf m st subst t) in
             VarMap.add x t subst)
        subst vbs
    in
    eval_whnf m st subst u
  | A.Bind (A.Fun,_,_) -> apply_subst subst t
  | A.Bind ((A.Forall | A.Exists) as b,v,body) ->
    let ty = A.Var.ty v in
    let dom =
      try A.Ty.Map.find ty m.domains
      with Not_found ->
        errorf "@[<2>could not find type %a in model@ stack %a@]"
          A.Ty.pp ty pp_stack st
    in
    (* expand into and/or over the domain *)
    let t' =
      let l =
        List.map
          (fun c_dom ->
             let subst' = VarMap.add v (lazy (A.const c_dom ty)) subst in
             eval_whnf m st subst' body)
          dom
      in
      begin match b with
        | A.Forall -> A.and_l l
        | A.Exists -> A.or_l l
        | _ -> assert false
      end
    in
    eval_whnf m st subst t'
  | A.Select (sel, u) ->
    let u = eval_whnf m st subst u in
    let t' = A.select ~ty:t.A.ty sel u in
    begin match as_cstor_app m.env u with
      | None -> t'
      | Some (cstor, _, args) ->
        if ID.equal cstor sel.A.select_cstor then (
          (* cstors match, take the argument *)
          assert (List.length args > sel.A.select_i);
          let new_t = List.nth args sel.A.select_i in
          eval_whnf m st subst new_t
        ) else (
          A.undefined_value t.A.ty
        )
    end
  | A.Match (u, branches) ->
    let u = eval_whnf m st subst u in
    begin match as_cstor_app m.env u with
      | None ->
        let branches =
          ID.Map.map
            (fun (vars,rhs) ->
               let subst, vars = rename_vars subst vars in
               vars, apply_subst subst rhs)
            branches
        in
        A.match_ u branches
      | Some (c, _, cstor_args) ->
        match ID.Map.get c branches with
          | None -> assert false
          | Some (vars, rhs) ->
            assert (List.length vars = List.length cstor_args);
            let subst' =
              List.fold_left2
                (fun s v arg ->
                   let arg' = lazy (apply_subst subst arg) in
                   VarMap.add v arg' s)
                subst vars cstor_args
            in
            eval_whnf m st subst' rhs
    end
  | A.Not f ->
    let f = eval_whnf m st subst f in
    begin match A.term_view f with
      | A.Bool true -> A.false_
      | A.Bool false -> A.true_
      | _ -> A.not_ f
    end
  | A.Asserting {t=u; guard=g} ->
    let g' = eval_whnf m st subst g in
    begin match A.term_view g' with
      | A.Bool true -> eval_whnf m st subst u
      | A.Bool false ->
        A.undefined_value u.A.ty (* assertion failed, uncharted territory! *)
      | _ -> A.asserting u g'
    end
  | A.Op (op, l) ->
    let l = List.map (eval_whnf m st subst) l in
    begin match op with
      | A.And ->
        if List.exists A.is_false l then A.false_
        else if List.for_all A.is_true l then A.true_
        else A.and_l l
      | A.Or ->
        if List.exists A.is_true l then A.true_
        else if List.for_all A.is_false l then A.false_
        else A.or_l l
      | A.Imply ->
        assert false (* TODO *)
      | A.Eq ->
        begin match l with
          | [] -> assert false
          | x :: tail ->
            if List.for_all (fun y -> equal_as_values x y = Eq) tail
            then A.true_
            else if List.exists (fun y -> equal_as_values x y = Neq) tail
            then A.false_
            else A.op A.Eq l
        end
      | A.Distinct ->
        if
          Sequence.diagonal_l l
          |> Sequence.exists (fun (t,u) -> equal_as_values t u = Eq)
        then A.false_
        else if
          Sequence.diagonal_l l
          |> Sequence.for_all (fun (t,u) -> equal_as_values t u = Neq)
        then A.true_
        else A.op A.Distinct l
    end
  | A.Arith (_, _) -> assert false (* TODO *)
(* beta-reduce [f l] while [f] is a function,constant or variable *)
and eval_whnf_app m st subst_f subst_l f l = match A.term_view f, l with
  | A.Bind (A.Fun,v, body), arg :: tail ->
    let subst_f = VarMap.add v (lazy (apply_subst subst_l arg)) subst_f in
    eval_whnf_app m st subst_f subst_l body tail
  | _ -> eval_whnf_app' m st subst_f subst_l f l
(* evaluate [f] and try to beta-reduce if [eval_whnf m f] is a function *)
and eval_whnf_app' m st subst_f subst_l f l =
  let f' = eval_whnf m st subst_f f in
  begin match A.term_view f', l with
    | A.Bind (A.Fun,_,_), _::_ ->
      eval_whnf_app m st subst_l subst_l f' l (* beta-reduce again *)
    | _ ->
      (* blocked *)
      let l = List.map (apply_subst subst_l) l in
      A.app f' l
  end

(* eval term [t] under model [m] *)
let eval (m:t) (t:term) = eval_whnf m [] empty_subst t
