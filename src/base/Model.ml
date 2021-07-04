(* This file is free software. See file "license" for more details. *)

open Base_types

module Val_map = struct
  module M = CCMap.Make(CCInt)
  module Key = struct
    type t = Value.t list
    let equal = CCList.equal Value.equal
    let hash = Hash.list Value.hash
  end
  type key = Key.t

  type 'a t = (key * 'a) list M.t

  let empty = M.empty
  let is_empty m = M.cardinal m = 0

  let cardinal = M.cardinal

  let find k m =
    try Some (CCList.assoc ~eq:Key.equal k @@ M.find (Key.hash k) m)
    with Not_found -> None

  let add k v m =
    let h = Key.hash k in
    let l = M.get_or ~default:[] h m in
    let l = CCList.Assoc.set ~eq:Key.equal k v l in
    M.add h l m

  let to_iter m yield = M.iter (fun _ l -> List.iter yield l) m
end

module Fun_interpretation = struct
  type t = {
    cases: Value.t Val_map.t;
    default: Value.t;
  }

  let default fi = fi.default
  let cases_list fi = Val_map.to_iter fi.cases |> Iter.to_rev_list

  let make ~default l : t =
    let m = List.fold_left (fun m (k,v) -> Val_map.add k v m) Val_map.empty l in
    { cases=m; default }
end

type t = {
  values: Value.t Term.Map.t;
  funs: Fun_interpretation.t Fun.Map.t;
}

let empty : t = {
  values=Term.Map.empty;
  funs=Fun.Map.empty;
}

(* FIXME: ues this to allocate a default value for each sort
    (* get or make a default value for this type *)
    let rec get_ty_default (ty:Ty.t) : Value.t =
      match Ty.view ty with
      | Ty_prop -> Value.true_
      | Ty_atomic { def = Ty_uninterpreted _;_} ->
        (* domain element *)
        Ty_tbl.get_or_add ty_tbl ~k:ty
          ~f:(fun ty -> Value.mk_elt (ID.makef "ty_%d" @@ Ty.id ty) ty)
      | Ty_atomic { def = Ty_def d; args; _} ->
        (* ask the theory for a default value *)
        Ty_tbl.get_or_add ty_tbl ~k:ty
          ~f:(fun _ty ->
            let vals = List.map get_ty_default args in
            d.default_val vals)
    in
   *)

let[@inline] mem t m = Term.Map.mem t m.values
let[@inline] find t m = Term.Map.get t m.values

let add t v m : t =
  match Term.Map.find t m.values with
  | v' ->
    if not @@ Value.equal v v' then (
      Error.errorf "@[Model: incompatible values for term %a@ :previous %a@ :new %a@]"
        Term.pp t Value.pp v Value.pp v'
    );
    m
  | exception Not_found ->
    {m with values=Term.Map.add t v m.values}

let add_fun c v m : t =
  match Fun.Map.find c m.funs with
  | _ -> Error.errorf "@[Model: function %a already has an interpretation@]" Fun.pp c
  | exception Not_found ->
    {m with funs=Fun.Map.add c v m.funs}

(* merge two models *)
let merge m1 m2 : t =
  let values = Term.Map.merge_safe m1.values m2.values
      ~f:(fun t o -> match o with
        | `Left v | `Right v -> Some v
        | `Both (v1,v2) ->
          if Value.equal v1 v2 then Some v1
          else (
            Error.errorf "@[Model: incompatible values for term %a@ :previous %a@ :new %a@]"
              Term.pp t Value.pp v1 Value.pp v2
          ))
  and funs =
    Fun.Map.merge_safe m1.funs m2.funs
      ~f:(fun c o -> match o with
        | `Left v | `Right v -> Some v
        | `Both _ ->
          Error.errorf "cannot merge the two interpretations of function %a" Fun.pp c)
  in
  {values; funs}

let add_funs fs m : t = merge {values=Term.Map.empty; funs=fs} m

let pp out {values; funs} =
  let module FI = Fun_interpretation in
  let pp_tv out (t,v) = Fmt.fprintf out "(@[%a@ := %a@])" Term.pp t Value.pp v in
  let pp_fun_entry out (vals,ret) =
    Format.fprintf out "(@[%a@ := %a@])" (Fmt.Dump.list Value.pp) vals Value.pp ret
  in
  let pp_fun out (c, fi: Fun.t * FI.t) =
    Format.fprintf out "(@[<hov>%a :default %a@ %a@])"
      Fun.pp c Value.pp fi.FI.default
      (Fmt.list ~sep:(Fmt.return "@ ") pp_fun_entry) (FI.cases_list fi) 
  in
  Fmt.fprintf out "(@[model@ @[:terms (@[<hv>%a@])@]@ @[:funs (@[<hv>%a@])@]@])"
    (Fmt.iter ~sep:Fmt.(return "@ ") pp_tv) (Term.Map.to_iter values)
    (Fmt.iter ~sep:Fmt.(return "@ ") pp_fun) (Fun.Map.to_iter funs)

exception No_value

let eval (m:t) (t:Term.t) : Value.t option =
  let module FI = Fun_interpretation in
  let rec aux t = match Term.view t with
    | Bool b -> Value.bool b
    | Not a ->
      begin match aux a with
        | V_bool b -> V_bool (not b)
        | v -> Error.errorf "@[Model: wrong value@ for boolean %a@ :val %a@]" Term.pp a Value.pp v
      end
    | Ite (a,b,c) ->
      begin match aux a with
        | V_bool true -> aux b
        | V_bool false -> aux c
        | v -> Error.errorf "@[Model: wrong value@ for boolean %a@ :val %a@]" Term.pp a Value.pp v
      end
    | Eq(a,b) ->
      let a = aux a in
      let b = aux b in
      if Value.equal a b then Value.true_ else Value.false_
    | LRA _l ->
      assert false
      (* TODO: evaluation
      begin match l with
        | LRA_pred (p, a, b) ->
        | LRA_op (_, _, _)|LRA_const _|LRA_other _ -> assert false
      end
      *)
    | App_fun (c, args) ->
      match Fun.view c, (args :_ IArray.t:> _ array) with
      | Fun_def udef, _ ->
        (* use builtin interpretation function *)
        let args = IArray.map aux args in
        udef.eval args
      | Fun_cstor c, _ ->
        Value.cstor_app c (IArray.to_list_map aux args)
      | Fun_select s, [|u|] ->
        begin match aux u with
          | V_cstor {c;args} when Cstor.equal c s.select_cstor ->
            List.nth args s.select_i
          | v_u ->
            Error.errorf "cannot eval selector %a@ on %a" Term.pp t Value.pp v_u
        end
      | Fun_is_a c1, [|u|] ->
        begin match aux u with
          | V_cstor {c=c2;args=_} ->
            Value.bool (Cstor.equal c1 c2)
          | v_u ->
            Error.errorf "cannot eval is-a %a@ on %a" Term.pp t Value.pp v_u
        end
      | Fun_select _, _ ->
        Error.errorf "bad selector term %a" Term.pp t
      | Fun_is_a _, _ ->
        Error.errorf "bad is-a term %a" Term.pp t
      | Fun_undef _, _ ->
        (try Term.Map.find t m.values
        with Not_found ->
          begin match Fun.Map.find c m.funs with
            | fi ->
              let args = IArray.map aux args |> IArray.to_list in
              begin match Val_map.find args fi.FI.cases with
                | None -> fi.FI.default
                | Some v -> v
              end
            | exception Not_found ->
              raise No_value (* no particular interpretation *)
          end)
  in
  try Some (aux t)
  with No_value -> None

(* TODO: get model from each theory, then complete it as follows based on types
  let mk_model (cc:t) (m:A.Model.t) : A.Model.t =
    let module Model = A.Model in
    let module Value = A.Value in
    Log.debugf 15 (fun k->k "(@[cc.mk-model@ %a@])" pp_full cc);
    let t_tbl = N_tbl.create 32 in
    (* populate [repr -> value] table *)
    T_tbl.values cc.tbl
      (fun r ->
         if N.is_root r then (
           (* find a value in the class, if any *)
           let v =
             N.iter_class r
             |> Iter.find_map (fun n -> Model.eval m n.n_term)
           in
           let v = match v with
             | Some v -> v
             | None ->
               if same_class r (true_ cc) then Value.true_
               else if same_class r (false_ cc) then Value.false_
               else Value.fresh r.n_term
           in
           N_tbl.add t_tbl r v
         ));
    (* now map every term to its representative's value *)
    let pairs =
      T_tbl.values cc.tbl
      |> Iter.map
        (fun n ->
           let r = find_ n in
           let v =
             try N_tbl.find t_tbl r
             with Not_found ->
               Error.errorf "didn't allocate a value for repr %a" N.pp r
           in
           n.n_term, v)
    in
    let m = Iter.fold (fun m (t,v) -> Model.add t v m) m pairs in
    Log.debugf 5 (fun k->k "(@[cc.model@ %a@])" Model.pp m);
    m
   *)
