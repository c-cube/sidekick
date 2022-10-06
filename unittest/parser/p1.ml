module P = Parse_term
module A = Ast_term

(*
let () = Printexc.record_backtrace true
*)

let () =
  Printexc.register_printer (function
    | Parser_comb.ParseError e -> Some (Parser_comb.Error.to_string e)
    | _ -> None)

let test_str what s =
  let t = P.of_string_exn s in

  Fmt.printf "%s: %a@." what A.pp_term t;
  Fmt.printf "loc(%s): %a@." what A.pp_loc (A.loc t)

let () = test_str "t1" "f (g x) y"
let () = test_str "t2" "let x:= 1 in f (f x 2)"
