module VVec = TVar.Vec_of

type t = { vars: VVec.t; levels: Veci.t }

let create () : t = { vars = VVec.create (); levels = Veci.create () }

let[@inline] push_assignment (self : t) (v : TVar.t) : unit =
  VVec.push self.vars v

let[@inline] var_at (self : t) (i : int) : TVar.t = VVec.get self.vars i
let[@inline] n_levels self = Veci.size self.levels
let push_level (self : t) : unit = Veci.push self.levels (VVec.size self.vars)

let pop_levels (self : t) (n : int) ~f : unit =
  if n <= n_levels self then (
    let idx = Veci.get self.levels n in
    Veci.shrink self.levels n;
    while VVec.size self.vars > idx do
      let elt = VVec.pop self.vars in
      f elt
    done
  )
