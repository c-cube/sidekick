
(** {1 Main for dimacs} *)

type 'a or_error = ('a, string) CCResult.t

let parse file : int list list or_error =
  try
    CCIO.with_in file
      (fun ic ->
         let lexbuf = Lexing.from_channel ic in
         Parser.file Lexer.token lexbuf)
    |> CCResult.return
  with e ->
    CCResult.of_exn_trace e

