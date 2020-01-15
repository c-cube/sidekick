
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun cond () Bool)
(declare-fun p (U) Bool)
(assert (and (= a b) (p a) (not (p (ite cond a b)))))
(check-sat)
