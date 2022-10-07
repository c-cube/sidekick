type position = Position.t
type t = { start: position; end_: position }

let mk ~start ~end_ : t = { start; end_ }

let pp out (self : t) =
  Fmt.fprintf out "%a - %a" Position.pp self.start Position.pp self.end_

let merge a b : t =
  { start = Position.min a.start b.start; end_ = Position.max a.end_ b.end_ }

let of_lexloc ((p1, p2) : Lexing.position * Lexing.position) : t =
  { start = Position.of_lexpos p1; end_ = Position.of_lexpos p2 }
