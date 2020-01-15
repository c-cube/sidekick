
; if + congruence
(declare-sort u 0)
(declare-fun p0 () Bool)
(declare-fun a () u)
(declare-fun b1 () u)
(declare-fun b2 () u)
(declare-fun c () u)
(declare-fun f (u) u)
(assert (= a (ite p0 b1 b2)))
(assert (= (f b1) c))
(assert (= (f b2) c))
(assert (not (= (f a) c)))
(check-sat)
