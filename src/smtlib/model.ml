open Sidekick_core
module T = Term
module TM = Term.Map

type value = Term.t
type fun_ = Term.t

module TL_map = CCMap.Make (struct
  type t = value list

  let compare = CCList.compare Term.compare
end)

type t = { m: value TL_map.t TM.t } [@@unboxed]

let empty : t = { m = T.Map.empty }
let is_empty self = T.Map.is_empty self.m
let iter_fun_entries (self : t) = TM.to_iter self.m
let get_fun_entries f self = TM.get f self.m

let get_fun_entry f vs self =
  match get_fun_entries f self with
  | None -> None
  | Some tm -> TL_map.get vs tm

let add_fun_entry f vs v self =
  let m = TM.get_or ~default:TL_map.empty f self.m in
  { m = TM.add f (TL_map.add vs v m) self.m }

let rec eval t (self : t) : value option =
  let eval_exn t =
    match eval t self with
    | Some v -> v
    | None -> raise Not_found
  in

  let f, args = Term.unfold_app t in
  match List.map eval_exn args with
  | exception Not_found -> None
  | v_args -> get_fun_entry f v_args self

let pp out (self : t) =
  if is_empty self then
    Fmt.string out "(model)"
  else (
    let rec pp_entries out = function
      | [] -> ()
      | ([], v) :: _ | [ (_, v) ] -> Term.pp out v
      | ((_ :: _ as vs), v) :: tl ->
        let pp_guard out () =
          match vs with
          | [] -> ()
          | [ t ] -> Fmt.fprintf out "(@[= x0 %a@])" Term.pp t
          | _ ->
            Fmt.fprintf out "(@[and@ ";
            List.iteri
              (fun i t -> Fmt.fprintf out "(@[= x%d %a@])" i Term.pp t)
              vs;
            Fmt.fprintf out "@])"
        in

        Fmt.fprintf out "(@[ite %a@ %a@ %a@])" pp_guard () Term.pp v pp_entries
          tl
    in
    let pp_fun out (f, entries) =
      match TL_map.choose_opt entries with
      | None -> ()
      | Some (args, v) ->
        let pp_arg out (i, ty) = Fmt.fprintf out "(@[x%d %a@])" i Term.pp ty in
        Fmt.fprintf out "(@[<1>define-fun %a (@[%a@])@ %a@ %a@])" Term.pp f
          (Util.pp_list ~sep:"" pp_arg)
          (List.mapi (fun i v -> i, Term.ty v) args)
          Term.pp (Term.ty v) pp_entries (TL_map.to_list entries)
    in
    Fmt.fprintf out "(@[<hv>model@ %a@])" (Util.pp_iter pp_fun)
      (TM.to_iter self.m)
  )
