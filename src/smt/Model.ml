
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

open Solver_types

type t = {
  values: Value.t Term.Map.t;
}

let empty : t = {values=Term.Map.empty}

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
    {values=Term.Map.add t v m.values}

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
  in
  {values}

let pp out (m:t) =
  let pp_tv out (t,v) = Fmt.fprintf out "(@[%a@ -> %a@])" Term.pp t Value.pp v in
  Fmt.fprintf out "(@[model@ %a@])"
    (Fmt.seq ~sep:Fmt.(return "@ ") pp_tv) (Term.Map.to_seq m.values)

exception No_value

let eval (m:t) (t:Term.t) : Value.t option =
  let rec aux t = match Term.view t with
    | Bool b -> Value.bool b
    | If (a,b,c) ->
      begin match aux a with
        | V_bool true -> aux b
        | V_bool false -> aux c
        | v -> Error.errorf "@[Model: wrong value@ for boolean %a@ %a@]" Term.pp a Value.pp v
      end
    | App_cst (c, args) ->
      begin try Term.Map.find t m.values
        with Not_found ->
        match Cst.view c with
        | Cst_def udef ->
          (* use builtin interpretation function *)
          let args = IArray.map aux args in
          udef.eval args
        | Cst_undef _ ->
          Log.debugf 5 (fun k->k "(@[model.eval.undef@ %a@])" Term.pp t);
          raise No_value (* no particular interpretation *)
      end
  in
  try Some (aux t)
  with No_value -> None
