
(declare-sort a 0)
(declare-fun x () a)
(declare-fun f (a) a)
(assert (= x (f x)))
(assert (not (= x (f (f (f x))))))
(check-sat)
