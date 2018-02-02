
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

open CDCL

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

let as_domain_elt env t = match A.term_view t with
  | A.Const id ->
    begin match A.env_find_def env id with
      | Some A.E_uninterpreted_cst -> Some id
      | _ -> None
    end
  | _ -> None

let pp_stack out (l:term list) : unit =
  let ppt out t = Format.fprintf out "(@[%a@ :ty %a@])" A.pp_term t A.Ty.pp t.A.ty in
  CCFormat.(within "[" "]" (hvbox (list ppt))) out l

let apply_subst (subst:subst) t =
  let rec aux subst t = match A.term_view t with
    | A.Var v ->
      begin match VarMap.get v subst with
        | None -> t
        | Some (lazy t') -> t'
      end
    | A.Undefined_value
    | A.Bool _ | A.Const _ | A.Unknown _ -> t
    | A.Select (sel, t) -> A.select sel (aux subst t) t.A.ty
    | A.App (f,l) -> A.app (aux subst f) (List.map (aux subst) l)
    | A.If (a,b,c) -> A.if_ (aux subst a) (aux subst b) (aux subst c)
    | A.Match (u,m) ->
      A.match_ (aux subst u)
        (ID.Map.map
           (fun (vars,rhs) ->
              let subst, vars = rename_vars subst vars in
              vars, aux subst rhs) m)
    | A.Switch (u,m) ->
      A.switch (aux subst u) (ID.Map.map (aux subst) m)
    | A.Let (x,t,u) ->
      let subst', x' = rename_var subst x in
      A.let_ x' (aux subst t) (aux subst' u)
    | A.Bind (A.Mu, _,_) -> assert false
    | A.Bind (b, x,body) ->
      let subst', x'  = rename_var subst x in
      A.bind ~ty:(A.ty t) b x' (aux subst' body)
    | A.Not f -> A.not_ (aux subst f)
    | A.Binop (op,a,b) -> A.binop op (aux subst a)(aux subst b)
    | A.Asserting (t,g) ->
      A.asserting (aux subst t)(aux subst g)
  in
  if VarMap.is_empty subst then t else aux subst t

(* Weak Head Normal Form.
   @param m the model
   @param st the "stack trace" (terms around currently being evaluated)
   @param t the term to eval *)
let rec eval_whnf (m:t) (st:term list) (subst:subst) (t:term): term =
  Log.debugf 5
    (fun k->k "%s@[<2>eval_whnf `@[%a@]`@ in @[%a@]@]"
        (String.make (List.length st) ' ') (* indent *)
        A.pp_term t pp_subst subst);
  let st = t :: st in
  try
    eval_whnf_rec m st subst t
  with A.Ill_typed msg ->
    errorf "@[<2>Model:@ internal type error `%s`@ in %a@]" msg pp_stack st
and eval_whnf_rec m st subst t = match A.term_view t with
  | A.Undefined_value | A.Bool _ | A.Unknown _ -> t
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
  | A.Let (x,t,u) ->
    let t = lazy (eval_whnf m st subst t) in
    let subst' = VarMap.add x t subst in
    eval_whnf m st subst' u
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
    let t' = A.select sel u t.A.ty in
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
  | A.Switch (u, map) ->
    let u = eval_whnf m st subst u in
    begin match as_domain_elt m.env u with
      | None ->
        let map = ID.Map.map (apply_subst subst) map in
        A.switch u map
      | Some cst ->
        begin match ID.Map.get cst map with
          | Some rhs -> eval_whnf m st subst rhs
          | None ->
            let map = ID.Map.map (apply_subst subst) map in
            A.switch u map
        end
    end
  | A.Not f ->
    let f = eval_whnf m st subst f in
    begin match A.term_view f with
      | A.Bool true -> A.false_
      | A.Bool false -> A.true_
      | _ -> A.not_ f
    end
  | A.Asserting (u, g) ->
    let g' = eval_whnf m st subst g in
    begin match A.term_view g' with
      | A.Bool true -> eval_whnf m st subst u
      | A.Bool false ->
        A.undefined_value u.A.ty (* assertion failed, uncharted territory! *)
      | _ -> A.asserting u g'
    end
  | A.Binop (op, a, b) ->
    let a = eval_whnf m st subst a in
    let b = eval_whnf m st subst b in
    begin match op with
      | A.And ->
        begin match A.term_view a, A.term_view b with
          | A.Bool true, A.Bool true -> A.true_
          | A.Bool false, _
          | _, A.Bool false -> A.false_
          | _ -> A.and_ a b
        end
      | A.Or ->
        begin match A.term_view a, A.term_view b with
          | A.Bool true, _
          | _, A.Bool true -> A.true_
          | A.Bool false, A.Bool false -> A.false_
          | _ -> A.or_ a b
        end
      | A.Imply ->
        begin match A.term_view a, A.term_view b with
          | _, A.Bool true
          | A.Bool false, _  -> A.true_
          | A.Bool true, A.Bool false -> A.false_
          | _ -> A.imply a b
        end
      | A.Eq ->
        begin match A.term_view a, A.term_view b with
          | A.Bool true, A.Bool true
          | A.Bool false, A.Bool false -> A.true_
          | A.Bool true, A.Bool false
          | A.Bool false, A.Bool true -> A.false_
          | A.Var v1, A.Var v2 when A.Var.equal v1 v2 -> A.true_
          | A.Const id1, A.Const id2 when ID.equal id1 id2 -> A.true_
          | _ ->
            begin match as_cstor_app m.env a, as_cstor_app m.env b with
              | Some (c1,_,l1), Some (c2,_,l2) ->
                if ID.equal c1 c2 then (
                  assert (List.length l1 = List.length l2);
                  eval_whnf m st subst (A.and_l (List.map2 A.eq l1 l2))
                ) else A.false_
              | _ ->
                begin match as_domain_elt m.env a, as_domain_elt m.env b with
                  | Some c1, Some c2 ->
                    (* domain elements: they are all distinct *)
                    if ID.equal c1 c2
                    then A.true_
                    else A.false_
                  | _ ->
                    A.eq a b
                end
            end
        end
    end
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
