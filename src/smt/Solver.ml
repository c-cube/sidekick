
(* This file is free software. See file "license" for more details. *)

(** {1 Main Solver} *)

open Solver_types

type term = Term.t
type cst = Cst.t
type ty = Ty.t
type ty_def = Solver_types.ty_def

type ty_cell = Solver_types.ty_cell =
  | Prop
  | Atomic of ID.t * ty_def
  | Arrow of ty * ty

let get_time : unit -> float = Sys.time

(** {2 The Main Solver} *)

type level = int

module Sat = CDCL.Make(Theory_combine)

(* main solver state *)
type t = {
  solver: Sat.t;
  stat: Stat.t;
  config: Config.t
}

let th_combine (self:t) : Theory_combine.t =
  Sat.theory self.solver

let create ?size ?(config=Config.empty) ~theories () : t =
  let self = {
    solver=Sat.create ?size ();
    stat=Stat.create ();
    config;
  } in
  (* now add the theories *)
  Theory_combine.add_theory_l (th_combine self) theories;
  self

(** {2 Sat Solver} *)

let print_progress (st:t) : unit =
  Printf.printf "\r[%.2f] expanded %d | clauses %d | lemmas %d%!"
    (get_time())
    st.stat.Stat.num_cst_expanded
    st.stat.Stat.num_clause_push
    st.stat.Stat.num_clause_tautology

let flush_progress (): unit =
  Printf.printf "\r%-80d\r%!" 0

(** {2 Toplevel Goals}

    List of toplevel goals to satisfy. Mainly used for checking purpose
*)

module Top_goals: sig
  val push : term -> unit
  val to_seq : term Sequence.t
  val check: unit -> unit
end = struct
  (* list of terms to fully evaluate *)
  let toplevel_goals_ : term list ref = ref []

  (* add [t] to the set of terms that must be evaluated *)
  let push (t:term): unit =
    toplevel_goals_ := t :: !toplevel_goals_;
    ()

  let to_seq k = List.iter k !toplevel_goals_

  (* FIXME
  (* check that this term fully evaluates to [true] *)
  let is_true_ (t:term): bool = match CC.normal_form t with
    | None -> false
    | Some (NF_bool b) -> b
    | Some (NF_cstor _) -> assert false (* not a bool *)

  let check () =
    if not (List.for_all is_true_ !toplevel_goals_)
    then (
      if Config.progress then flush_progress();
      Log.debugf 1
        (fun k->
           let pp_lit out t =
             let nf = CC.normal_form t in
             Format.fprintf out "(@[term: %a@ nf: %a@])"
               Term.pp t (Fmt.opt pp_term_nf) nf
           in
           k "(@[<hv1>Top_goals.check@ (@[<v>%a@])@])"
             (Util.pp_list pp_lit) !toplevel_goals_);
      assert false;
    )
  *)

  let check () : unit = ()
end

(** {2 Conversion} *)

(* list of constants we are interested in *)
let model_support_ : Cst.t list ref = ref []

let model_env_ : Ast.env ref = ref Ast.env_empty

let add_cst_support_ (c:cst): unit =
  CCList.Ref.push model_support_ c

let add_ty_support_ (_ty:Ty.t): unit = ()

(* FIXME: do this in another module, perhaps?
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
        with Not_found -> Util.errorf "type %a not in ty_tbl" ID.pp id
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

(** {2 Result} *)

type unknown =
  | U_timeout
  | U_max_depth
  | U_incomplete

type model = Model.t
let pp_model = Model.pp

type res =
  | Sat of model
  | Unsat (* TODO: proof *)
  | Unknown of unknown

(* FIXME: repair this and output a nice model.
module Model_build : sig
  val make: unit -> model

  val check : model -> unit
end = struct
  module ValueListMap = CCMap.Make(struct
      type t = Term.t list (* normal forms *)
      let compare = CCList.compare Term.compare
    end)

  type doms = {
    dom_of_ty: ID.t list Ty.Tbl.t; (* uninterpreted type -> domain elements *)
    dom_of_class: term Term.Tbl.t; (* representative -> normal form *)
    dom_of_cst: term Cst.Tbl.t; (* cst -> its normal form *)
    dom_of_fun: term ValueListMap.t Cst.Tbl.t; (* function -> args -> normal form *)
    dom_traversed: unit Term.Tbl.t; (* avoid cycles *)
  }

  let create_doms() : doms =
    { dom_of_ty=Ty.Tbl.create 32;
      dom_of_class = Term.Tbl.create 32;
      dom_of_cst=Cst.Tbl.create 32;
      dom_of_fun=Cst.Tbl.create 32;
      dom_traversed=Term.Tbl.create 128;
    }

  (* pick a term belonging to this type.
     we just generate a new constant, as picking true/a constructor might
     refine the partial model into an unsatisfiable state. *)
  let pick_default ~prefix (doms:doms)(ty:Ty.t) : term =
    (* introduce a fresh constant for this equivalence class *)
    let elts = Ty.Tbl.get_or ~default:[] doms.dom_of_ty ty in
    let cst = ID.makef "%s%s_%d" prefix (Ty.mangle ty) (List.length elts) in
    let nf = Term.const (Cst.make_undef cst ty) in
    Ty.Tbl.replace doms.dom_of_ty ty (cst::elts);
    nf

  (* follow "normal form" pointers deeply in the term *)
  let deref_deep (doms:doms) (t:term) : term =
    let rec aux t =
      let repr = (CC.find t :> term) in
      (* if not already done, traverse all parents to update the functions'
         models *)
      if not (Term.Tbl.mem doms.dom_traversed repr) then (
        Term.Tbl.add doms.dom_traversed repr ();
        Bag.to_seq repr.term_parents |> Sequence.iter aux_ignore;
      );
      (* find a normal form *)
      let nf: term =
        begin match CC.normal_form t with
          | Some (NF_bool true) -> Term.true_
          | Some (NF_bool false) -> Term.false_
          | Some (NF_cstor (cstor, args)) ->
            (* cstor applied to sub-normal forms *)
            Term.app_cst cstor.cstor_cst (IArray.map aux args)
          | None ->
            let repr = (CC.find t :> term) in
            begin match Term.Tbl.get doms.dom_of_class repr with
              | Some u -> u
              | None when Ty.is_uninterpreted t.term_ty ->
                let nf = pick_default ~prefix:"$" doms t.term_ty in
                Term.Tbl.add doms.dom_of_class repr nf;
                nf
              | None ->
                let nf = pick_default ~prefix:"?" doms t.term_ty in
                Term.Tbl.add doms.dom_of_class repr nf;
                nf
            end
        end
      in
      (* update other tables *)
      begin match t.term_cell with
        | True | False -> assert false (* should have normal forms *)
        | Fun _ | DB _ | Mu _
          -> ()
        | Builtin b -> ignore (Term.map_builtin aux b)
        | If (a,b,c) -> aux_ignore a; aux_ignore b; aux_ignore c
        | App_ho (f, l) -> aux_ignore f; List.iter aux_ignore l
        | Case (t, m) -> aux_ignore t; ID.Map.iter (fun _ rhs -> aux_ignore rhs) m
        | App_cst (f, a) when IArray.is_empty a ->
          (* remember [f := c] *)
          Cst.Tbl.replace doms.dom_of_cst f nf
        | App_cst (f, a) ->
          (* remember [f a := c] *)
          let a_values = IArray.map aux a |> IArray.to_list in
          let map =
            Cst.Tbl.get_or ~or_:ValueListMap.empty doms.dom_of_fun f
          in
          Cst.Tbl.replace doms.dom_of_fun f (ValueListMap.add a_values nf map)
      end;
      nf
    and aux_ignore t =
      ignore (aux t)
    in
    aux t

  (* TODO: maybe we really need a notion of "Undefined" that is
           also not a domain element (i.e. equality not defined on it)
           + some syntax for it *)

  (* build the model of a function *)
  let model_of_fun (doms:doms) (c:cst): Ast.term =
    let ty_args, ty_ret = Ty.unfold (Cst.ty c) in
    assert (ty_args <> []);
    let vars =
      List.mapi
        (fun i ty -> Ast.Var.make (ID.makef "x_%d" i) (Conv.ty_to_ast ty))
        ty_args
    in
    let default = match ty_ret.ty_cell with
      | Prop -> Ast.true_ (* should be safe: we would have split it otherwise *)
      | _ ->
        (* TODO: what about other finites types? *)
        pick_default ~prefix:"?" doms ty_ret |> Conv.term_to_ast
    in
    let cases =
      Cst.Tbl.get_or ~or_:ValueListMap.empty doms.dom_of_fun c
      |> ValueListMap.to_list
      |> List.map
        (fun (args,rhs) ->
           assert (List.length ty_args = List.length vars);
           let tests =
             List.map2
               (fun v arg -> Ast.eq (Ast.var v) (Conv.term_to_ast arg))
               vars args
           in
           Ast.and_l tests, Conv.term_to_ast rhs)
    in
    (* decision tree for the body *)
    let body =
      List.fold_left
        (fun else_ (test, then_) -> Ast.if_ test then_ else_)
        default cases
    in
    Ast.fun_l vars body

  let make () : model =
    let env = !model_env_ in
    let doms = create_doms () in
    (* compute values of meta variables *)
    let consts =
      !model_support_
      |> Sequence.of_list
      |> Sequence.filter_map
        (fun c ->
           if Ty.is_arrow (Cst.ty c) then None
           else
             (* find normal form of [c] *)
             let t = Term.const c in
             let t = deref_deep doms t |> Conv.term_to_ast in
             Some (c.cst_id, t))
      |> ID.Map.of_seq
    in
    (* now compute functions (the previous "deref_deep" have updated their use cases)  *)
    let consts =
      !model_support_
      |> Sequence.of_list
      |> Sequence.filter_map
        (fun c ->
           if Ty.is_arrow (Cst.ty c)
           then (
             let t = model_of_fun doms c in
             Some (c.cst_id, t)
           ) else None)
      |> ID.Map.add_seq consts
    in
    (* now we can convert domains *)
    let domains =
      Ty.Tbl.to_seq doms.dom_of_ty
      |> Sequence.filter_map
        (fun (ty,dom) ->
           if Ty.is_uninterpreted ty
           then Some (Conv.ty_to_ast ty, List.rev dom)
           else None)
      |> Ast.Ty.Map.of_seq
    (* and update env: add every domain element to it *)
    and env =
      Ty.Tbl.to_seq doms.dom_of_ty
      |> Sequence.flat_map_l (fun (_,dom) -> dom)
      |> Sequence.fold
        (fun env id -> Ast.env_add_def env id Ast.E_uninterpreted_cst)
        env
    in
    Model.make ~env ~consts ~domains

  let check m =
    Log.debugf 1 (fun k->k "checking model…");
    Log.debugf 5 (fun k->k "(@[<1>candidate model: %a@])" Model.pp m);
    let goals =
      Top_goals.to_seq
      |> Sequence.map Conv.term_to_ast
      |> Sequence.to_list
    in
    Model.check m ~goals
end
   *)

(** {2 Main} *)

let[@inline] clause_of_mclause (c:Sat.clause): Clause.t =
  Sat.Clause.atoms_l c |> Clause.make

(* convert unsat-core *)
let clauses_of_unsat_core (core:Sat.clause list): Clause.t Sequence.t =
  Sequence.of_list core
  |> Sequence.map clause_of_mclause

(* print all terms reachable from watched literals *)
let pp_term_graph _out (_:t) =
  ()

let pp_stats out (s:t) : unit =
  Format.fprintf out
    "(@[<hv1>stats@ \
     :num_expanded %d@ \
     :num_uty_expanded %d@ \
     :num_clause_push %d@ \
     :num_clause_tautology %d@ \
     :num_propagations %d@ \
     :num_unif %d@ \
     @])"
    s.stat.Stat.num_cst_expanded
    s.stat.Stat.num_uty_expanded
    s.stat.Stat.num_clause_push
    s.stat.Stat.num_clause_tautology
    s.stat.Stat.num_propagations
    s.stat.Stat.num_unif

let do_on_exit ~on_exit =
  List.iter (fun f->f()) on_exit;
  ()

let add_statement_l (_:t) _ = ()
(* FIXME
   Conv.add_statement_l
   *)

(* TODO: move this into submodule *)
let pp_proof out p =
  let pp_step_res out p =
    let {Sat.Proof.conclusion; _ } = Sat.Proof.expand p in
    let conclusion = clause_of_mclause conclusion in
    Clause.pp out conclusion
  in
  let pp_step out = function
    | Sat.Proof.Lemma _ -> Format.fprintf out "(@[<1>lemma@ ()@])"
    | Sat.Proof.Resolution (p1, p2, _) ->
      Format.fprintf out "(@[<1>resolution@ %a@ %a@])"
        pp_step_res p1 pp_step_res p2
    | _ -> Fmt.string out "<other>"
  in
  Format.fprintf out "(@[<v>";
  Sat.Proof.fold
    (fun () {Sat.Proof.conclusion; step } ->
       let conclusion = clause_of_mclause conclusion in
       Format.fprintf out "(@[<hv1>step@ %a@ @[<1>from:@ %a@]@])@,"
         Clause.pp conclusion pp_step step)
    () p;
  Format.fprintf out "@])";
  ()

(*
type unsat_core = Sat.clause list
   *)

(* TODO: main loop with iterative deepening of the unrolling  limit
   (not the value depth limit) *)
let solve ?on_exit:(_=[]) ?check:(_=true) (_self:t) : res =
  Unknown U_incomplete

(* FIXME
(* TODO: max_depth should actually correspond to the maximum depth
   of un-expanded terms (expand in body of t --> depth = depth(t)+1),
   so it corresponds to unfolding call graph to some depth *)

let solve ?(on_exit=[]) ?(check=true) () =
  let n_iter = ref 0 in
  let rec check_cc (): res =
    assert (Backtrack.at_level_0 ());
    if !n_iter > Config.max_depth then Unknown U_max_depth (* exceeded limit *)
    else begin match CC.check () with
      | CC.Unsat _ -> Unsat (* TODO proof *)
      | CC.Sat lemmas  ->
        add_cc_lemmas lemmas;
        check_solver()
    end

  and check_solver (): res =
    (* assume all literals [expanded t] are false *)
    let assumptions =
      Terms_to_expand.to_seq
      |> Sequence.map (fun {Terms_to_expand.lit; _} -> Lit.neg lit)
      |> Sequence.to_rev_list
    in
    incr n_iter;
    Log.debugf 2
      (fun k->k
          "(@[<1>@{<Yellow>solve@}@ @[:with-assumptions@ (@[%a@])@ n_iter: %d]@])"
          (Util.pp_list Lit.pp) assumptions !n_iter);
    begin match M.solve ~assumptions() with
      | M.Sat _ ->
        Log.debugf 1 (fun k->k "@{<Yellow>** found SAT@}");
        do_on_exit ~on_exit;
        let m = Model_build.make () in
        if check then Model_build.check m;
        Sat m
      | M.Unsat us ->
        let p = us.SI.get_proof () in
        Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
        let core = p |> M.unsat_core in
        (* check if unsat because of assumptions *)
        expand_next core
    end

  (* pick a term to expand, or UNSAT *)
  and expand_next (core:unsat_core) =
    begin match find_to_expand core with
      | None -> Unsat (* TODO proof *)
      | Some to_expand ->
        let t = to_expand.Terms_to_expand.term in
        Log.debugf 2 (fun k->k "(@[<1>@{<green>expand_next@}@ :term %a@])" Term.pp t);
        CC.expand_term t;
        Terms_to_expand.remove t;
        Clause.push_new (Clause.make [to_expand.Terms_to_expand.lit]);
        Backtrack.backtrack_to_level_0 ();
        check_cc () (* recurse *)
    end
  in
  check_cc()

   *)
