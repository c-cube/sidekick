
(set-logic QF_LRA)
(declare-const a Real)
(assert (= (* 3 a) 5))
(check-sat)
(get-model)
