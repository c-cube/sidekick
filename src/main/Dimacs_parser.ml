module L = Dimacs_lexer

type t = {
  buf: Lexing.lexbuf;
  mutable header: (int * int) option;
}

let create (ic:in_channel) : t =
  let buf = Lexing.from_channel ic in
  {buf; header=None}

let parse_header self =
  match self.header with
  | Some tup -> tup
  | None ->
    let i, j =
      try
        (match L.token self.buf with
         | L.P ->
           (match L.token self.buf with
            | L.CNF ->
              (match L.token self.buf with
               | L.LIT i ->
                 (match L.token self.buf with
                  | L.LIT j -> i,j
                  | _ -> raise Exit)
               | _ -> raise Exit)
            | _ -> raise Exit)
         | _ -> raise Exit
        )
      with Exit -> Error.errorf "expected file to start with header"
    in
    self.header <- Some (i,j);
    i,j

let next_clause self : _ option =
  let rec loop acc = match L.token self.buf with
    | L.EOF when acc=[] -> None
    | L.EOF -> Error.errorf "unexpected EOF in a clause"
    | L.ZERO -> Some (List.rev acc)
    | L.LIT i -> loop (i::acc)
    | _ -> Error.errorf "expected clause"
  in
  loop []

let iter self k =
  ignore (parse_header self : _*_);
  let rec loop () =
    match next_clause self with
    | None -> ()
    | Some c -> k c; loop ()
  in
  loop ()

