type entry_view = Entry_view.t

module type OPS = sig
  val write : entry_view -> Write_value.t
end

type ops = (module OPS)
type t = { view: entry_view; ops: ops }
