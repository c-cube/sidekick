module P = Parse_util
module A = Ast_term

(*
let () = Printexc.record_backtrace true
*)

let () =
  Printexc.register_printer (function
    | P.Exn_parse_error e -> Some (P.Error.to_string e)
    | _ -> None)

let test_term_str what s =
  let t = P.term_of_string s in
  match t with
  | Ok t ->
    Fmt.printf "%s: %a@." what A.pp_term t;
    Fmt.printf "loc(%s): %a@." what Loc.pp (A.loc t)
  | Error err ->
    Fmt.printf "FAIL:@ error while parsing %S:@ %a@." what P.Error.pp err

let () = test_term_str "t1" "f (g x) y"
let () = test_term_str "t2" "let x:= 1 in f (f x 2)"

let () =
  test_term_str "t3"
    {|let l := map f (list 1 2 3) in
let l2 := rev l in rev l2 = l|}

let () =
  test_term_str "t4" {|let assm := is_foo p ==> (filter p l = nil) in true|}

let () =
  test_term_str "t5"
    {|let f := fn (x y : int) (z:bool). ( x+ y) = z
      and g := fn x. f (f x) in is_g g|}

let test_decl what s =
  let t = P.decls_of_string s in
  match t with
  | Ok l ->
    Fmt.printf "@[<v2>%s:@ %a@]@." what (Util.pp_list ~sep:"" A.pp_decl) l
  | Error err ->
    Fmt.printf "FAIL:@ error while parsing %S:@ %a@." what P.Error.pp err

let () =
  test_decl "d1"
    {|def f (x y:list int) : list int := if (x = 0) y whatever;
    #ty f;
    #sledgehammer fn x y. f x y = f x y;
  |}
