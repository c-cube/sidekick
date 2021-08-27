(** {1 Process Statements} *)

module Loc = Smtlib_utils.V_2_6.Loc
module Parse_ast = Smtlib_utils.V_2_6.Ast
module Process = Process
module Solver = Process.Solver
module Term = Sidekick_base.Term
module Stmt = Sidekick_base.Statement
module Proof = Sidekick_base.Proof_stub

type 'a or_error = ('a, string) CCResult.t

module Parse = struct
  let parse_chan_exn ?(filename="<no name>") ic =
    let lexbuf = Lexing.from_channel ic in
    Loc.set_file lexbuf filename;
    Smtlib_utils.V_2_6.(Parser.parse_list Lexer.token) lexbuf

  let parse_file_exn file : Parse_ast.statement list =
    CCIO.with_in file (parse_chan_exn ~filename:file)

  let parse_file_exn ctx file : Stmt.t list =
    (* delegate parsing to [Tip_parser] *)
    parse_file_exn file
    |> CCList.flat_map (Typecheck.conv_statement ctx)

  let parse tst file =
    let ctx = Typecheck.Ctx.create tst in
    try Result.Ok (parse_file_exn ctx file)
    with e -> Result.Error (Printexc.to_string e)

  let parse_stdin tst =
    let ctx = Typecheck.Ctx.create tst in
    try
      parse_chan_exn ~filename:"<stdin>" stdin
      |> CCList.flat_map (Typecheck.conv_statement ctx)
      |> CCResult.return
    with e -> Result.Error (Printexc.to_string e)
end

let parse = Parse.parse
let parse_stdin = Parse.parse_stdin
