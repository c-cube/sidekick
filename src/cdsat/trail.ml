module VVec = TVar.Vec_of

type t = { vars: VVec.t; levels: Veci.t; mutable head: int }

let create () : t = { vars = VVec.create (); levels = Veci.create (); head = 0 }

let[@inline] push_assignment (self : t) (v : TVar.t) : unit =
  VVec.push self.vars v

let[@inline] get (self : t) (i : int) : TVar.t = VVec.get self.vars i
let[@inline] size (self : t) : int = VVec.size self.vars
let[@inline] n_levels self = Veci.size self.levels

let[@inline] push_level (self : t) : unit =
  Veci.push self.levels (VVec.size self.vars)

let[@inline] head self = self.head
let[@inline] set_head self n = self.head <- n

let pop_levels (self : t) (n : int) ~f : unit =
  if n <= n_levels self then (
    let idx = Veci.get self.levels n in
    Veci.shrink self.levels n;
    while VVec.size self.vars > idx do
      let elt = VVec.pop self.vars in
      f elt
    done;
    (* also reset head *)
    if self.head > idx then self.head <- idx
  )

let pp_full vst out (self : t) : unit =
  Fmt.fprintf out "(@[<hv>trail@ %a@])"
    (Util.pp_iter (TVar.pp_with_assignment vst))
    (VVec.to_iter self.vars)
