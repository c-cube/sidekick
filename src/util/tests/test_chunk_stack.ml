module A = Alcotest
module C = Chunk_stack

let l : unit Alcotest.test_case list ref = ref []
let ( ~! ) = Printf.sprintf "at line %d"
let mk_test ?(speed = `Quick) name f = l := (name, speed, f) :: !l

let () =
  mk_test "inbuf" @@ fun () ->
  let buf = C.Buf.create () in

  let writer = C.Writer.into_buf buf in
  C.Writer.add_string writer "hello";
  C.Writer.add_string writer "world";
  C.Writer.add_string writer "!!\x00!";

  let reader = C.Reader.from_buf buf in
  A.check
    A.(option string)
    ~!__LINE__ (Some "!!\x00!")
    (C.Reader.next_string reader);
  A.check
    A.(option string)
    ~!__LINE__ (Some "world")
    (C.Reader.next_string reader);
  A.check
    A.(option string)
    ~!__LINE__ (Some "hello")
    (C.Reader.next_string reader);
  A.check A.(option string) ~!__LINE__ None (C.Reader.next_string reader);
  ()

let () =
  mk_test ~speed:`Slow "infile" @@ fun () ->
  CCIO.File.with_temp ~prefix:"sidekick-test" ~suffix:"dat" (fun file ->
      CCIO.with_out file (fun oc ->
          let writer = C.Writer.into_channel oc in
          C.Writer.add_string writer "hello";
          C.Writer.add_string writer "world";
          C.Writer.add_string writer "!!\x00!");

      C.Reader.with_file_backward file (fun reader ->
          A.check
            A.(option string)
            ~!__LINE__ (Some "!!\x00!")
            (C.Reader.next_string reader);
          A.check
            A.(option string)
            ~!__LINE__ (Some "world")
            (C.Reader.next_string reader);
          A.check
            A.(option string)
            ~!__LINE__ (Some "hello")
            (C.Reader.next_string reader);
          A.check
            A.(option string)
            ~!__LINE__ None
            (C.Reader.next_string reader));
      ())

let tests = "chunk_stack", !l
