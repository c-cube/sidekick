(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(set-info :source |modified from smtlib.626179.smt2|)
(set-info :status unsat)
(declare-fun f3 () Real)
(declare-fun f4 () Real)
(assert (not (=> (< f3 f4) (=> (< f4 (* 2.0 f3)) (< 0.0 (- f4 f3))))))
(check-sat)
(exit)
