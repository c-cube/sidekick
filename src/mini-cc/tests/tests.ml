open Sidekick_util
open Sidekick_base

module A = Alcotest
module CC = Sidekick_mini_cc.Make(struct
  module T = Sidekick_base.Arg
  let cc_view = Term.cc_view
end)

module Setup() = struct
  let tst = Term.create()
  let (@->) l ret = Ty.Fun.mk l ret
  let ty_i = Ty.atomic_uninterpreted (ID.make "$i")
  let ty_bool = Ty.bool ()

  let fun_f = Fun.mk_undef (ID.make "f") ([ty_i] @-> ty_i)
  let fun_g = Fun.mk_undef (ID.make "g") ([ty_i; ty_i] @-> ty_i)
  let fun_p = Fun.mk_undef (ID.make "p") ([ty_i] @-> ty_bool)
  let fun_a = Fun.mk_undef_const (ID.make "a") ty_i
  let fun_b = Fun.mk_undef_const (ID.make "b") ty_i
  let fun_c = Fun.mk_undef_const (ID.make "c") ty_i
  let fun_d1 = Fun.mk_undef_const (ID.make "d1") ty_i
  let fun_d2 = Fun.mk_undef_const (ID.make "d2") ty_i

  let true_ = Term.true_ tst
  let false_ = Term.false_ tst
  let const c = Term.const tst c
  let app_a f l = Term.app_fun tst f l
  let app_l f l = Term.app_fun tst f (IArray.of_list l)
  let not_ x = Term.not_ tst x
  let eq a b = Term.eq tst a b
  let neq a b = Term.not_ tst (eq a b)
  let ite a b c = Term.ite tst a b c
  let a = const fun_a
  let b = const fun_b
  let c = const fun_c
  let d1 = const fun_d1
  let d2 = const fun_d2
  let f t1 = app_l fun_f [t1]
  let g t1 t2 = app_l fun_g [t1;t2]
  let p t1 = app_l fun_p [t1]
end

let l = ref []
let mk_test name f =
  l := (name, `Quick, f) :: !l

let () = mk_test "test_p_a_b" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.(p a) true;
  CC.add_lit cc S.(p b) false;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(eq a b) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = mk_test "test_p_a_b_2" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.(p a) true;
  CC.add_lit cc S.(not_ @@ p b) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(eq a b) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = mk_test "test_f_f_f_a" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.(neq a (f (f (f (f (f (f a))))))) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(eq a (f a)) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = mk_test "test_repeated_f_f_f_a" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  for _i = 0 to 10 do
    CC.add_lit cc S.(neq a (f (f (f (f (f (f a))))))) true;
    A.(check bool) "is-sat" (CC.check_sat cc) true;
    CC.add_lit cc S.(eq a (f a)) true;
    A.(check bool) "is-unsat" (CC.check_sat cc) false;
    CC.clear cc;
  done;
  ()

let () = mk_test "test_trans" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.(eq a b) true;
  CC.add_lit cc S.(eq b c) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.(neq (f a) (f c)) true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = mk_test "test_true" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.true_ true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  CC.add_lit cc S.false_ true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = mk_test "test_repeated_true" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  for _i = 0 to 10 do
    CC.add_lit cc S.true_ true;
    A.(check bool) "is-sat" (CC.check_sat cc) true;
    CC.add_lit cc S.false_ true;
    A.(check bool) "is-unsat" (CC.check_sat cc) false;
    CC.clear cc;
  done;
  ()

let () = mk_test "test_false" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.false_ true;
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

let () = mk_test "test_not_false" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.(not_ false_) true;
  A.(check bool) "is-sat" (CC.check_sat cc) true;
  ()

let () = mk_test "test_ite" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  for _i = 0 to 10 do
    CC.add_lit cc S.(eq a b) true;
    CC.add_lit cc S.(p (ite (eq a c) d1 d2)) true;
    CC.add_lit cc S.(not_ (p d1)) true;
    CC.add_lit cc S.(p d2) true;
    A.(check bool) "is-sat" (CC.check_sat cc) true;
    CC.add_lit cc S.(eq b c) true; (* force (p d1) *)
    A.(check bool) "is-unsat" (CC.check_sat cc) false;
    CC.clear cc;
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
let () = mk_test "test_reg_1" @@ fun () ->
  let module S = Setup() in
  let cc = CC.create S.tst in
  CC.add_lit cc S.(eq a (g a c)) true;
  CC.add_lit cc S.(eq b (g a c)) true;
  CC.add_lit cc S.(eq c (g c b)) true;
  CC.add_lit cc S.(eq a (g c c)) true;
  CC.add_lit cc S.(eq (g c (g c b)) (g (g c c) b)) true;
  CC.add_lit cc S.(eq (g a b) (g a c)) false; (* goal *)
  A.(check bool) "is-unsat" (CC.check_sat cc) false;
  ()

(* run alcotest *)
let () = Alcotest.run "mini-cc-tests" ["mini-cc", List.rev !l]
