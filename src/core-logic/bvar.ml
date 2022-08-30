open Types_

type t = bvar = { bv_idx: int; bv_ty: term }

let equal (v1 : t) v2 = v1.bv_idx = v2.bv_idx && Term_.equal v1.bv_ty v2.bv_ty
let hash v = H.combine2 (H.int v.bv_idx) (Term_.hash v.bv_ty)
let pp out v = Fmt.fprintf out "bv[%d]" v.bv_idx
let[@inline] ty self = self.bv_ty
let make i ty : t = { bv_idx = i; bv_ty = ty }
