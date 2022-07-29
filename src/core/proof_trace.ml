type lit = Lit.t
type step_id = int32
type proof_term = Proof_term.t

module Step_vec = struct
  type elt = step_id
  type t = elt Vec.t

  let get = Vec.get
  let size = Vec.size
  let iter = Vec.iter
  let iteri = Vec.iteri
  let create ?cap:_ () = Vec.create ()
  let clear = Vec.clear
  let copy = Vec.copy
  let is_empty = Vec.is_empty
  let push = Vec.push
  let fast_remove = Vec.fast_remove
  let filter_in_place = Vec.filter_in_place
  let ensure_size v len = Vec.ensure_size v ~elt:0l len
  let pop = Vec.pop_exn
  let set = Vec.set
  let shrink = Vec.shrink
  let to_iter = Vec.to_iter
end

module type DYN = sig
  val enabled : unit -> bool
  val add_step : proof_term -> step_id
  val add_unsat : step_id -> unit
  val delete : step_id -> unit
end

type t = (module DYN)

let[@inline] enabled ((module Tr) : t) : bool = Tr.enabled ()
let[@inline] add_step ((module Tr) : t) rule : step_id = Tr.add_step rule
let[@inline] add_unsat ((module Tr) : t) s : unit = Tr.add_unsat s
let[@inline] delete ((module Tr) : t) s : unit = Tr.delete s
let make (d : (module DYN)) : t = d
let dummy_step_id : step_id = -1l

let dummy : t =
  (module struct
    let enabled () = false
    let add_step _ = dummy_step_id
    let add_unsat _ = ()
    let delete _ = ()
  end)
