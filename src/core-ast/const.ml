type view = ..

module type DYN_OPS = sig
  val pp : view Fmt.printer
  val equal : view -> view -> bool
  val hash : view -> int
end

type ops = (module DYN_OPS)
type t = { view: view; ops: ops }

let view self = self.view

let equal (a : t) b =
  let (module O) = a.ops in
  O.equal a.view b.view

let hash (a : t) : int =
  let (module O) = a.ops in
  O.hash a.view

let pp out (a : t) =
  let (module O) = a.ops in
  O.pp out a.view

let make view ops : t = { view; ops }
