
module A = Alcotest

let spf = Printf.sprintf
let msgline line = spf "test at line %d" line
let alco_mk name f = name, `Quick, f

module BV = Bitvec

let t1 = alco_mk "mkgetset" @@ fun () ->
  let bv = BV.create() in
  BV.ensure_size bv 200;
  A.(check bool) (msgline __LINE__) false (BV.get bv 0);
  A.(check bool) (msgline __LINE__) false (BV.get bv 1);
  for i=30 to 150 do
    A.(check bool) (msgline __LINE__) false (BV.get bv i);
  done;

  BV.set bv 25 true;
  BV.set bv 1 true;
  BV.set bv 127 true;
  BV.set bv 126 true;
  BV.set bv 126 false;

  for i=0 to 150 do
    A.(check bool) (msgline __LINE__) (i=1||i=25||i=127) (BV.get bv i);
  done;
  ()

let tests = "bitvec", [t1]
