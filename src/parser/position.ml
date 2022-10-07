type t = { file: string; line: int; col: int }

let line self = self.line
let col self = self.col
let ( <= ) x y = x.line < y.line || (x.line = y.line && x.col <= y.col)
let ( < ) x y = x.line < y.line || (x.line = y.line && x.col < y.col)
let ( >= ) a b = b <= a
let ( > ) a b = b < a

let min a b =
  if a <= b then
    a
  else
    b

let max a b =
  if a >= b then
    a
  else
    b

let pp out self = Format.fprintf out "at line %d, column %d" self.line self.col

(** Build position from a lexing position *)
let of_lexpos (p : Lexing.position) : t =
  { file = p.pos_fname; line = p.pos_lnum; col = p.pos_cnum - p.pos_bol }
