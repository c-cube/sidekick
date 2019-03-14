
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert
  (and
   (= p (= a b))
   (= (not p) (= b a))))
(check-sat)
; :status unsat
