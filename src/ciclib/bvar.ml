open Types_

type t = bvar = { bv_idx: int } [@@unboxed]

let equal (v1 : t) v2 = v1.bv_idx = v2.bv_idx
let hash v = H.combine2 10 (H.int v.bv_idx)
let pp out v = Fmt.fprintf out "bv[%d]" v.bv_idx
let[@inline] idx self = self.bv_idx
let make i : t = { bv_idx = i }
