(** Entry to be written.

    This is used when producing a trace, to emit a new entry.
*)

type entry_view = Entry_view.t

(** Dynamic operations for {!t} *)
module type OPS = sig
  val write : entry_view -> Write_value.t

  (*
  val pp : entry_view Fmt.printer
  *)
  (* TODO: read *)
end

type ops = (module OPS)

type t = { view: entry_view; ops: ops }
(** A single entry to be written into the trace.

    A trace is consistuted of entries, numbered
    from [0] to [n], in the order of their production.
    The number has no semantics besides a form of
    causal order.
*)
