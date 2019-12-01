
(set-info :status unsat)
(declare-datatypes ((three 0)) (((A) (B) (C))))
(declare-const t1 three)
(declare-const t2 three)
(declare-const t3 three)
(declare-const t4 three)

(assert (distinct t1 t2 t3 t4))

(check-sat)
