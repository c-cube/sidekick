open Sigs
module T = Term
module TM = Term.Map

type t = {
  tst: Term.store;
  mutable m: Term.t TM.t;
  required: Term.t Queue.t;
  gensym: Gensym.t;
}

let create tst : t =
  { tst; m = TM.empty; required = Queue.create (); gensym = Gensym.create tst }

let pp out (self : t) : unit =
  let pp_kv out (k, v) =
    Fmt.fprintf out "(@[%a@ := %a@])" Term.pp k Term.pp v
  in
  Fmt.fprintf out "(@[model-builder@ :model %a@ :q (@[%a@])@])"
    (Util.pp_iter pp_kv) (TM.to_iter self.m) (Util.pp_iter T.pp)
    (Iter.of_queue self.required)

let gensym self ~pre ~ty : Term.t = Gensym.fresh_term self.gensym ~pre ty

let rec pop_required (self : t) : _ option =
  match Queue.take_opt self.required with
  | None -> None
  | Some t when TM.mem t self.m -> pop_required self
  | Some t -> Some t

let require_eval (self : t) t : unit =
  if not @@ TM.mem t self.m then Queue.push t self.required

let[@inline] mem self t : bool = TM.mem t self.m

let add (self : t) ?(subs = []) t v : unit =
  if not @@ mem self t then (
    self.m <- TM.add t v self.m;
    List.iter (fun u -> require_eval self u) subs
  )

type eval_cache = Term.Internal_.cache

let create_cache = Term.Internal_.create_cache

let eval_opt ?(cache = Term.Internal_.create_cache 8) (self : t) (t : Term.t) =
  match TM.get t self.m with
  | None -> None
  | Some t ->
    Some
      (T.Internal_.replace_ ~cache self.tst ~recursive:true t
         ~f:(fun ~recurse:_ u -> TM.get u self.m))

let eval ?(cache = Term.Internal_.create_cache 8) (self : t) (t : Term.t) =
  let t = TM.get t self.m |> Option.value ~default:t in
  T.Internal_.replace_ ~cache self.tst ~recursive:true t ~f:(fun ~recurse:_ u ->
      TM.get u self.m)

let to_map ?(cache = T.Internal_.create_cache 8) (self : t) : _ TM.t =
  (* ensure we evaluate each term only once by using a cache *)
  let map =
    TM.keys self.m
    |> Iter.map (fun t -> t, eval ~cache self t)
    |> Iter.fold (fun m (t, v) -> TM.add t v m) TM.empty
  in
  map
