
module L = Drup_lexer

type event =
  | Add of int list
  | Delete of int list

type t = {
  buf: Lexing.lexbuf;
}

let create (ic:in_channel) : t =
  let buf = Lexing.from_channel ic in
  {buf; }

let next self : _ option =
  let rec get_clause acc = match L.token self.buf with
    | L.EOF -> Error.errorf "unexpected EOF in a clause"
    | L.ZERO -> List.rev acc
    | L.LIT i -> get_clause (i::acc)
    | _ -> Error.errorf "expected clause"
  in
  begin match L.token self.buf with
    | L.EOF -> None
    | L.D ->
      let c = get_clause [] in
      Some (Delete c)
    | L.ZERO -> Some (Add [])
    | L.LIT i ->
      let c = get_clause [i] in
      Some (Add c)
  end

let iter self k =
  let rec loop () =
    match next self with
    | None -> ()
    | Some ev -> k ev; loop ()
  in
  loop ()

