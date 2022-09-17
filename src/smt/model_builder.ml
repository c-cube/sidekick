open Sigs
module T = Term

type t = {
  tst: Term.store;
  mutable m: Model.t;
  required: Term.t Queue.t;
  gensym: Gensym.t;
}

let create tst : t =
  {
    tst;
    m = Model.empty;
    required = Queue.create ();
    gensym = Gensym.create tst;
  }

let pp out (self : t) : unit =
  Fmt.fprintf out "(@[model-builder@ :model %a@ :q (@[%a@])@])" Model.pp self.m
    (Util.pp_iter T.pp)
    (Iter.of_queue self.required)

let gensym self ~pre ~ty : Term.t = Gensym.fresh_term self.gensym ~pre ty

let rec pop_required (self : t) : _ option =
  match Queue.take_opt self.required with
  | None -> None
  | Some t when Model.mem self.m t -> pop_required self
  | Some t -> Some t

let require_eval (self : t) t : unit =
  if not @@ Model.mem self.m t then Queue.push t self.required

let[@inline] mem self t : bool = Model.mem self.m t

let add (self : t) ?(subs = []) t v : unit =
  if not @@ mem self t then (
    self.m <- Model.add t v self.m;
    List.iter (fun u -> require_eval self u) subs
  )

type eval_cache = Term.Internal_.cache

let eval ?(cache = Term.Internal_.create_cache 8) (self : t) (t : Term.t) =
  let t = Model.find self.m t |> Option.value ~default:t in
  T.Internal_.replace_ ~cache self.tst ~recursive:true t ~f:(fun ~recurse:_ u ->
      Model.find self.m u)

let to_model (self : t) : Model.t =
  (* ensure we evaluate each term only once *)
  let cache = T.Internal_.create_cache 8 in
  let m =
    Model.keys self.m
    |> Iter.map (fun t -> t, eval ~cache self t)
    |> Iter.fold (fun m (t, v) -> Model.add t v m) Model.empty
  in
  m
