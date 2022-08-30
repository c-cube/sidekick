open! Sidekick_base
module A = Alcotest

(* *)

module T = Term
module CC = Sidekick_mini_cc

module Setup () = struct
  let tst = Term.Store.create ()
  let ( @-> ) l ret = Term.arrow_l tst l ret
  let ty_i = Uconst.uconst_of_id tst (ID.make "$i") (Term.type_ tst)
  let ty_bool = Ty.bool tst
  let fun_f = Uconst.uconst_of_id tst (ID.make "f") ([ ty_i ] @-> ty_i)
  let fun_g = Uconst.uconst_of_id tst (ID.make "g") ([ ty_i; ty_i ] @-> ty_i)
  let fun_p = Uconst.uconst_of_id tst (ID.make "p") ([ ty_i ] @-> ty_bool)
  let a = Uconst.uconst_of_id tst (ID.make "a") ty_i
  let b = Uconst.uconst_of_id tst (ID.make "b") ty_i
  let c = Uconst.uconst_of_id tst (ID.make "c") ty_i
  let d1 = Uconst.uconst_of_id tst (ID.make "d1") ty_i
  let d2 = Uconst.uconst_of_id tst (ID.make "d2") ty_i
  let true_ = Term.true_ tst
  let false_ = Term.false_ tst
  let const c = Term.const tst c
  let app_l f l = Term.app_l tst f l
  let not_ x = Term.not tst x
  let eq a b = Term.eq tst a b
  let neq a b = Term.not tst (eq a b)
  let ite a b c = Term.ite tst a b c
  let f t1 = app_l fun_f [ t1 ]
  let g t1 t2 = app_l fun_g [ t1; t2 ]
  let p t1 = app_l fun_p [ t1 ]
end

let l : unit Alcotest.test_case list ref = ref []
let mk_test name f = l := (name, `Quick, f) :: !l

let () =
  mk_test "test_p_a_b" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.(p a) true;
  CC.add_lit cc S.(p b) false;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(eq a b) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () =
  mk_test "test_p_a_b_2" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.(p a) true;
  CC.add_lit cc S.(not_ @@ p b) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(eq a b) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () =
  mk_test "test_f_f_f_a" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.(neq a (f (f (f (f (f (f a))))))) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(eq a (f a)) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () =
  mk_test "test_repeated_f_f_f_a" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  for _i = 0 to 10 do
    CC.add_lit cc S.(neq a (f (f (f (f (f (f a))))))) true;
    A.(check bool) "is-sat" (CC.check_sat cc) true;
    CC.add_lit cc S.(eq a (f a)) true;
    A.(check bool) "is-unsat" (CC.check_sat cc) false;
    CC.clear cc
  done;
  ()

let () =
  mk_test "test_trans" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.(eq a b) true;
  CC.add_lit cc S.(eq b c) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(neq (f a) (f c)) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () =
  mk_test "test_true" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.true_ true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.false_ true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () =
  mk_test "test_repeated_true" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  for _i = 0 to 10 do
    CC.add_lit cc S.true_ true;
    A.(check bool) "is-sat" (CC.check_sat cc) true;
    CC.add_lit cc S.false_ true;
    A.(check bool) "is-unsat" (CC.check_sat cc) false;
    CC.clear cc
  done;
  ()

let () =
  mk_test "test_false" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.false_ true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () =
  mk_test "test_not_false" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.(not_ false_) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  ()

let () =
  mk_test "test_ite" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  for _i = 0 to 10 do
    CC.add_lit cc S.(eq a b) true;
    CC.add_lit cc S.(p (ite (eq a c) d1 d2)) true;
    CC.add_lit cc S.(not_ (p d1)) true;
    CC.add_lit cc S.(p d2) true;
    A.(check bool) "is-sat" (CC.check_sat cc) true;
    CC.add_lit cc S.(eq b c) true;
    (* force (p d1) *)
    A.(check bool) "is-unsat" (CC.check_sat cc) false;
    CC.clear cc
  done;
  ()

(* from the following PO:
    `cl (- a = (g a c)),
        (- b = (g a c)),
        (- c = (g c b)),
        (- a = (g c c)),
        (- (g c (g c b)) = (g (g c c) b)),
        (+ (g a b) = (g a c))))`
*)
let () =
  mk_test "test_reg_1" @@ fun () ->
  let module S = Setup () in
  let cc = CC.create_default S.tst in
  CC.add_lit cc S.(eq a (g a c)) true;
  CC.add_lit cc S.(eq b (g a c)) true;
  CC.add_lit cc S.(eq c (g c b)) true;
  CC.add_lit cc S.(eq a (g c c)) true;
  CC.add_lit cc S.(eq (g c (g c b)) (g (g c c) b)) true;
  CC.add_lit cc S.(eq (g a b) (g a c)) false;
  (* goal *)
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = Alcotest.run ~and_exit:true "mini-cc tests" [ "mini-cc", !l ]
