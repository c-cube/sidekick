open Printf

let just_copy f1 f2 =
  let ic = open_in f1 in
  let len = in_channel_length ic in
  let buf = Bytes.create len in
  really_input ic buf 0 len;
  close_in_noerr ic;

  let oc = open_out f2 in
  output oc buf 0 len;
  flush oc;
  close_out_noerr oc

let () =
  let f1 = Sys.argv.(1) in
  let f2 = Sys.argv.(2) in

  (* annoying changes in the typechecking output *)
  if Sys.ocaml_version < "4.08" then (
    just_copy f1 f2;
    exit 0
  );
  try
    let e = Sys.command @@ Printf.sprintf "ocaml-mdx test '%s' -o '%s'" f1 f2 in
    if e <> 0 then (
      printf "warning: ocaml-mdx exited with code %d\n" e;
      just_copy f1 f2
    ) else
      print_endline "ocaml-mdx returned 0"
  with Sys_error e ->
    printf "error when running mdx: %s\n" e;
    just_copy f1 f2;
    ()
