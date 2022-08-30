open Sidekick_core
open Sigs
module T = Term

type t = {
  tst: Term.store;
  m: Term.t T.Tbl.t;
  required: Term.t Queue.t;
  gensym: Gensym.t;
}

let create tst : t =
  {
    tst;
    m = T.Tbl.create 8;
    required = Queue.create ();
    gensym = Gensym.create tst;
  }

let pp out (self : t) : unit =
  let pp_pair out (t, v) = Fmt.fprintf out "(@[%a :=@ %a@])" T.pp t T.pp v in
  Fmt.fprintf out "(@[model-builder@ :m (@[%a@])@ :q (@[%a@])@])"
    (Util.pp_iter pp_pair) (T.Tbl.to_iter self.m) (Util.pp_iter T.pp)
    (Iter.of_queue self.required)

let gensym self ~pre ~ty : Term.t = Gensym.fresh_term self.gensym ~pre ty

let rec pop_required (self : t) : _ option =
  match Queue.take_opt self.required with
  | None -> None
  | Some t when T.Tbl.mem self.m t -> pop_required self
  | Some t -> Some t

let require_eval (self : t) t : unit =
  if not @@ T.Tbl.mem self.m t then Queue.push t self.required

let mem self t : bool = T.Tbl.mem self.m t

let add (self : t) ?(subs = []) t v : unit =
  assert (not @@ T.Tbl.mem self.m t);
  T.Tbl.add self.m t v;
  List.iter (fun u -> require_eval self u) subs;
  ()

type eval_cache = Term.Internal_.cache

let eval ?(cache = Term.Internal_.create_cache 8) (self : t) (t : Term.t) =
  let t = try T.Tbl.find self.m t with Not_found -> t in
  T.Internal_.replace_ ~cache self.tst ~recursive:true t ~f:(fun ~recurse:_ u ->
      T.Tbl.find_opt self.m u)

let to_model (self : t) : Model.t =
  (* ensure we evaluate each term only once *)
  let cache = T.Internal_.create_cache 8 in
  let tbl =
    T.Tbl.keys self.m
    |> Iter.map (fun t -> t, eval ~cache self t)
    |> T.Tbl.of_iter
  in
  Model.Internal_.of_tbl tbl
