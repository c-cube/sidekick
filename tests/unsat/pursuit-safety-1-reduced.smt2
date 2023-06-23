(declare-const p Bool)
(declare-const x Real)
(assert (and (= x (ite p 1 0.0)) (= 0.0 (ite p 1 (+ 1 x)))))
(check-sat)
