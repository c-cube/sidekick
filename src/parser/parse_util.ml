module Error = struct
  type t = { loc: Loc.t; msg: string }

  (* TODO: use pp_loc *)

  let mk ~loc msg : t = { msg; loc }

  let pp out (self : t) =
    Fmt.fprintf out "parse error: %s@ %a" self.msg Loc.pp self.loc

  let to_string = Fmt.to_string pp
end

exception Exn_parse_error of Error.t

open struct
  module A = Ast_term

  let guard buf f =
    try f ()
    with Parse.Error ->
      let loc =
        Loc.of_lexloc (Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf)
      in
      raise (Exn_parse_error (Error.mk ~loc @@ "syntax error"))
end

let term_of_string_exn ?filename (s : string) : A.term =
  let buf = Lexing.from_string s in
  let@ () = guard buf in
  Option.iter (Lexing.set_filename buf) filename;
  Parse.top_term Lex.token buf

let term_of_string ?filename (s : string) : _ result =
  try Ok (term_of_string_exn ?filename s) with Exn_parse_error e -> Error e

let decls_of_string_exn ?filename (s : string) : A.decl list =
  let buf = Lexing.from_string s in
  let@ () = guard buf in
  Option.iter (Lexing.set_filename buf) filename;
  Parse.top_decls Lex.token buf

let decls_of_string ?filename (s : string) : _ result =
  try Ok (decls_of_string_exn ?filename s) with Exn_parse_error e -> Error e
