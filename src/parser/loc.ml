module Input : sig
  type t

  val string : string -> t
  val file : string -> t
  val to_pploc_input : t -> Pp_loc.Input.t
end = struct
  include Pp_loc.Input

  let to_pploc_input x = x
end

type position = Position.t
type t = { start: position; end_: position }

let mk ~start ~end_ : t = { start; end_ }

let pp out (self : t) =
  Fmt.fprintf out "%a - %a" Position.pp self.start Position.pp self.end_

let merge a b : t =
  { start = Position.min a.start b.start; end_ = Position.max a.end_ b.end_ }

let of_lexloc ((p1, p2) : Lexing.position * Lexing.position) : t =
  { start = Position.of_lexpos p1; end_ = Position.of_lexpos p2 }

(** Pretty print using pp_loc *)
let pp_loc ?max_lines ~(input : Input.t) out (l : t list) : unit =
  let input = Input.to_pploc_input input in
  let to_pploc (self : t) : Pp_loc.loc =
    Position.to_pploc_pos self.start, Position.to_pploc_pos self.end_
  in
  let l = List.map to_pploc l in

  Pp_loc.pp ?max_lines ~input out l
