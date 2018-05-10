
(** {1 Process Statements} *)

module Fmt = CCFormat
module Ast = Sidekick_smt.Ast
module E = CCResult
module Loc = Locations
module Process = Process

type 'a or_error = ('a, string) CCResult.t

module Parse = struct
  let parse_chan_exn ?(filename="<no name>") ic =
    let lexbuf = Lexing.from_channel ic in
    Loc.set_file lexbuf filename;
    Parser.parse_list Lexer.token lexbuf

  let parse_chan ?filename ic =
    try Result.Ok (parse_chan_exn ?filename ic)
    with e -> Result.Error (Printexc.to_string e)

  let parse_file_exn file : Parse_ast.statement list =
    CCIO.with_in file (parse_chan_exn ~filename:file)

  let parse_file file =
    try Result.Ok (parse_file_exn file)
    with e -> Result.Error (Printexc.to_string e)

  let parse_file_exn ctx file : Ast.statement list =
    (* delegate parsing to [Tip_parser] *)
    parse_file_exn file
    |> CCList.flat_map (Typecheck.conv_statement ctx)

  let parse file =
    let ctx = Typecheck.Ctx.create () in
    try Result.Ok (parse_file_exn ctx file)
    with e -> Result.Error (Printexc.to_string e)

  let parse_stdin () =
    let ctx = Typecheck.Ctx.create () in
    try
      parse_chan_exn ~filename:"<stdin>" stdin
      |> CCList.flat_map (Typecheck.conv_statement ctx)
      |> CCResult.return
    with e -> Result.Error (Printexc.to_string e)
end

let parse = Parse.parse
let parse_stdin = Parse.parse_stdin
