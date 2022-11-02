type t = TVar.reason =
  | Decide of { level: int }
  | Propagate of {
      level: int;
      hyps: TVar.Vec_of.t;
      proof: Sidekick_proof.step_id;
    }

let pp out (self : t) : unit =
  match self with
  | Decide { level } -> Fmt.fprintf out "decide[lvl=%d]" level
  | Propagate { level; hyps; proof = _ } ->
    Fmt.fprintf out "(@[propagate[lvl=%d]@ :n-hyps %d@])" level
      (TVar.Vec_of.size hyps)

let[@inline] decide level : t = Decide { level }
let[@inline] propagate_ level v proof : t = Propagate { level; hyps = v; proof }

let[@inline] level self =
  match self with
  | Decide d -> d.level
  | Propagate p -> p.level

let propagate_v store v proof : t =
  let level =
    TVar.Vec_of.fold_left (fun l v -> max l (TVar.level store v)) 0 v
  in
  propagate_ level v proof

let propagate_l store l proof : t =
  let v = TVar.Vec_of.create ~cap:(List.length l) () in
  List.iter (TVar.Vec_of.push v) l;
  propagate_v store v proof
