(set-logic QF_UFDT)
(declare-datatypes ((t 0))
  (((T0) (T1 (prev1 t)) (T2 (prev2 t)))))

(declare-const c1 t)
(declare-const c2 t)
(declare-const c3 t)
(declare-const c4 t)
(declare-const c5 t)
(declare-const c6 t)
(declare-const c7 t)
(declare-const c8 t)
(declare-const c9 t)
(declare-const c10 t)
(declare-const c11 t)
(declare-const c12 t)
(declare-const c13 t)
(declare-const c14 t)
(declare-const c15 t)
(declare-const c16 t)
(declare-const c17 t)
(declare-const c18 t)
(declare-const c19 t)
(declare-const c20 t)
(assert (= c1 c20))
(assert (not (= c1 T0)))
(assert (not (= c2 T0)))
(assert (not (= c3 T0)))
(assert (not (= c4 T0)))
(assert (not (= c5 T0)))
(assert (not (= c6 T0)))
(assert (not (= c7 T0)))
(assert (not (= c8 T0)))
(assert (not (= c9 T0)))
(assert (not (= c10 T0)))
(assert (not (= c11 T0)))
(assert (not (= c12 T0)))
(assert (not (= c13 T0)))
(assert (not (= c14 T0)))
(assert (not (= c15 T0)))
(assert (not (= c16 T0)))
(assert (not (= c17 T0)))
(assert (not (= c18 T0)))
(assert (not (= c19 T0)))
(assert (not (= c20 T0)))
(assert (or (= c1 (T1 c2)) (= c1 (T2 c2))))
(assert (or (= c2 (T1 c3)) (= c2 (T2 c3))))
(assert (or (= c3 (T1 c4)) (= c3 (T2 c4))))
(assert (or (= c4 (T1 c5)) (= c4 (T2 c5))))
(assert (or (= c5 (T1 c6)) (= c5 (T2 c6))))
(assert (or (= c6 (T1 c7)) (= c6 (T2 c7))))
(assert (or (= c7 (T1 c8)) (= c7 (T2 c8))))
(assert (or (= c8 (T1 c9)) (= c8 (T2 c9))))
(assert (or (= c9 (T1 c10)) (= c9 (T2 c10))))
(assert (or (= c10 (T1 c11)) (= c10 (T2 c11))))
(assert (or (= c11 (T1 c12)) (= c11 (T2 c12))))
(assert (or (= c12 (T1 c13)) (= c12 (T2 c13))))
(assert (or (= c13 (T1 c14)) (= c13 (T2 c14))))
(assert (or (= c14 (T1 c15)) (= c14 (T2 c15))))
(assert (or (= c15 (T1 c16)) (= c15 (T2 c16))))
(assert (or (= c16 (T1 c17)) (= c16 (T2 c17))))
(assert (or (= c17 (T1 c18)) (= c17 (T2 c18))))
(assert (or (= c18 (T1 c19)) (= c18 (T2 c19))))
(assert (or (= c19 (T1 c20)) (= c19 (T2 c20))))
(check-sat)
(exit)

