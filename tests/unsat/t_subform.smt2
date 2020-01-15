
(set-info :status "unsat")
(declare-fun p () Bool)
(declare-sort u 0)
(declare-fun f (Bool) u)
(declare-const a u)
(declare-const b u)
(assert (distinct a b))

(assert (= (f p) a))
(assert (= (f (and p (or p p))) b))
(check-sat)
