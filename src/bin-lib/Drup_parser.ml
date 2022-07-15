module L = Drup_lexer

type event = Input of int list | Add of int list | Delete of int list
type t = { buf: Lexing.lexbuf }

let create_string s : t = { buf = Lexing.from_string s }
let create_chan (ic : in_channel) : t = { buf = Lexing.from_channel ic }

let next self : _ option =
  let rec get_clause acc =
    match L.token self.buf with
    | L.EOF -> Error.errorf "unexpected EOF in a clause"
    | L.ZERO -> List.rev acc
    | L.LIT i -> get_clause (i :: acc)
    | _ -> Error.errorf "expected clause"
  in
  match L.token self.buf with
  | L.EOF -> None
  | L.I ->
    let c = get_clause [] in
    Some (Input c)
  | L.D ->
    let c = get_clause [] in
    Some (Delete c)
  | L.R ->
    let c = get_clause [] in
    Some (Add c)
  | L.ZERO -> Some (Add [])
  | L.LIT i ->
    let c = get_clause [ i ] in
    Some (Add c)

let iter self k =
  let rec loop () =
    match next self with
    | None -> ()
    | Some ev ->
      k ev;
      loop ()
  in
  loop ()
