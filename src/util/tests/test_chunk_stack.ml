
module A = Alcotest
module C = Chunk_stack

let l : unit Alcotest.test_case list ref = ref []

let (~!) = Printf.sprintf "at line %d"
let mk_test name f =
  l := (name, `Quick, f) :: !l

let () = mk_test "inbuf" @@ fun () ->
  let buf = C.Buf.create() in

  let writer = C.Writer.into_buf buf in
  C.Writer.add_string writer "hello";
  C.Writer.add_string writer "world";
  C.Writer.add_string writer "!!\x00!";

  let reader = C.Reader.from_buf buf in
  A.check A.(option string) ~!__LINE__ (Some "!!\x00!") (C.Reader.next_string reader);
  A.check A.(option string) ~!__LINE__ (Some "world") (C.Reader.next_string reader);
  A.check A.(option string) ~!__LINE__ (Some "hello") (C.Reader.next_string reader);
  A.check A.(option string) ~!__LINE__ None (C.Reader.next_string reader);
  ()

let tests = "chunk_stack", !l
