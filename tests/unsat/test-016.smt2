
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert
  (and
   (= p (= a b))
   (= q (= b a))
   (or (not p) (not q))
   (or p q)))
(check-sat)
; :status unsat
