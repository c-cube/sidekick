
; expect: unsat
; intermediate problem in tests/unsat/clocksynchro_2clocks.worst_case_skew.base.smt2

(set-logic QF_LRA)
(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)

(assert (< (+ (/ 2335 666) x_5 x_6 (* (/ 2 999) x_7) (* (/ 2 999) x_4)) 0))
(assert (<= (+ (- (/ 1001 1000)) (* -1 x_0) x_2) 0))
(assert (<= (+ (/ 999 1000) x_0 (* -1 x_2)) 0))
(assert (<= (+ (- (/ 1001 1000)) (* -1 x_0) x_1) 0))
(assert (<= (+ (/ 999 1000) x_0 (- 0 x_1)) 0))
(assert (= x_0 0))
(assert
  (<= (+
    (/ 1502501 999000)
    (* (/ 1001 999) x_5)
    (* (/ 1001 999) x_6)
    (* -1 x_7)
    (* (/ 1001 999) x_3))
    0))

(assert (< (+ (/ 1001 2) (* (/ 999 2) x_6) x_7 (* (/ -999 2) x_4)) 0))
(assert (<= (+ (/ 1001 999) x_5 (* -1 x_6) (* (/ 1001 1998) x_4)) 0))
(assert (< (* -1 x_5) 0))
(assert (< (* -1 x_4) 0))
(assert (< (* -1 x_3) 0))

(check-sat)
