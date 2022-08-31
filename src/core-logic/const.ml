open Types_

type view = const_view = ..

module type DYN_OPS = sig
  val pp : view Fmt.printer
  val equal : view -> view -> bool
  val hash : view -> int
  val opaque_to_cc : view -> bool
end

type ops = (module DYN_OPS)
type t = const = { c_view: view; c_ops: ops; c_ty: term }

let[@inline] view self = self.c_view
let[@inline] ty self = self.c_ty

let equal (a : t) b =
  let (module O) = a.c_ops in
  O.equal a.c_view b.c_view && Term_.equal a.c_ty b.c_ty

let hash (a : t) : int =
  let (module O) = a.c_ops in
  H.combine2 (O.hash a.c_view) (Term_.hash a.c_ty)

let pp out (a : t) =
  let (module O) = a.c_ops in
  O.pp out a.c_view

let make c_view c_ops ~ty:c_ty : t = { c_view; c_ops; c_ty }
