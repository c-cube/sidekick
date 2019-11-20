
(set-info :status unsat)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))

(assert (= (succ (succ zero)) (succ zero)))
(check-sat)
