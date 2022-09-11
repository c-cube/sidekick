
; falsly declared unsat. minimized
; from tests/sat/QF_UF_schedule_world.2.prop1_ab_cti_max.smt2 using ddSMT .
(declare-fun p () Bool)
(declare-fun y () Bool)
(assert (= false (not p)))
(assert p)
(assert (= y p))
(assert y)
(check-sat)
