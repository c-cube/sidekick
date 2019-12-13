

(declare-sort a 0)
(declare-fun x () a)
(declare-fun y () a)
(declare-fun f (a) a)
(declare-fun p1 () Bool)
(assert (= x y))
(assert (or p1 (= y (f x))))
(assert (or (not p1) (= y (f (f x)))))
(assert (not (= x (f (f (f (f (f (f x)))))))))
(check-sat)
