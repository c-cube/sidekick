
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

open Solver_types

module Val_map = struct
  module M = CCIntMap
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
    try Some (CCList.assoc ~eq:Key.equal k @@ M.find_exn (Key.hash k) m)
    with Not_found -> None

  let add k v m =
    let h = Key.hash k in
    let l = M.find h m |> CCOpt.get_or ~default:[] in
    let l = CCList.Assoc.set ~eq:Key.equal k v l in
    M.add h l m

  let to_seq m yield = M.iter (fun _ l -> List.iter yield l) m
end

module Fun_interpretation = struct
  type t = {
    cases: Value.t Val_map.t;
    default: Value.t;
  }

  let default fi = fi.default
  let cases_list fi = Val_map.to_seq fi.cases |> Iter.to_rev_list

  let make ~default l : t =
    let m = List.fold_left (fun m (k,v) -> Val_map.add k v m) Val_map.empty l in
    { cases=m; default }
end

type t = {
  values: Value.t Term.Map.t;
  funs: Fun_interpretation.t Cst.Map.t;
}

let empty : t = {
  values=Term.Map.empty;
  funs=Cst.Map.empty;
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
  match Cst.Map.find c m.funs with
  | _ -> Error.errorf "@[Model: function %a already has an interpretation@]" Cst.pp c
  | exception Not_found ->
    {m with funs=Cst.Map.add c v m.funs}

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
    Cst.Map.merge_safe m1.funs m2.funs
      ~f:(fun c o -> match o with
        | `Left v | `Right v -> Some v
        | `Both _ ->
          Error.errorf "cannot merge the two interpretations of function %a" Cst.pp c)
  in
  {values; funs}

let add_funs fs m : t = merge {values=Term.Map.empty; funs=fs} m

let pp out {values; funs} =
  let module FI = Fun_interpretation in
  let pp_tv out (t,v) = Fmt.fprintf out "(@[%a@ := %a@])" Term.pp t Value.pp v in
  let pp_fun_entry out (vals,ret) =
    Format.fprintf out "(@[%a@ := %a@])" (Fmt.Dump.list Value.pp) vals Value.pp ret
  in
  let pp_fun out (c, fi: Cst.t * FI.t) =
    Format.fprintf out "(@[<hov>%a :default %a@ %a@])"
      Cst.pp c Value.pp fi.FI.default
      (Fmt.list ~sep:(Fmt.return "@ ") pp_fun_entry) (FI.cases_list fi) 
  in
  Fmt.fprintf out "(@[model@ @[:terms (@[<hv>%a@])@]@ @[:funs (@[<hv>%a@])@]@])"
    (Fmt.seq ~sep:Fmt.(return "@ ") pp_tv) (Term.Map.to_seq values)
    (Fmt.seq ~sep:Fmt.(return "@ ") pp_fun) (Cst.Map.to_seq funs)

exception No_value

let eval (m:t) (t:Term.t) : Value.t option =
  let module FI = Fun_interpretation in
  let rec aux t = match Term.view t with
    | Bool b -> Value.bool b
    | If (a,b,c) ->
      begin match aux a with
        | V_bool true -> aux b
        | V_bool false -> aux c
        | v -> Error.errorf "@[Model: wrong value@ for boolean %a@ %a@]" Term.pp a Value.pp v
      end
    | Not a ->
      begin match aux a with
        | V_bool b -> V_bool (not b)
        | v -> Error.errorf "@[Model: wrong value@ for boolean %a@ :val %a@]" Term.pp a Value.pp v
      end
    | Eq(a,b) ->
      let a = aux a in
      let b = aux b in
      if Value.equal a b then Value.true_ else Value.false_
    | App_cst (c, args) ->
      match Cst.view c with
      | Cst_def udef ->
        (* use builtin interpretation function *)
        let args = IArray.map aux args in
        udef.eval args
      | Cst_undef _ ->
        try Term.Map.find t m.values
        with Not_found ->
          begin match Cst.Map.find c m.funs with
            | fi ->
              let args = IArray.map aux args |> IArray.to_list in
              begin match Val_map.find args fi.FI.cases with
                | None -> fi.FI.default
                | Some v -> v
              end
            | exception Not_found ->
              raise No_value (* no particular interpretation *)
          end
  in
  try Some (aux t)
  with No_value -> None
