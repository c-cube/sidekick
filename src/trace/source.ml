type tag = string

module type S = sig
  val get_entry : Entry_id.t -> tag * Ser_value.t
  val iter_all : (Entry_id.t -> tag:tag -> Ser_value.t -> unit) -> unit
end

type t = (module S)

let get_entry_exn (module S : S) id = S.get_entry id

let get_entry (module S : S) id : _ option =
  try Some (S.get_entry id) with Not_found -> None

let iter_all (module S : S) f : unit = S.iter_all f
