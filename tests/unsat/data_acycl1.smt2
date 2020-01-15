
(set-info :status unsat)
(declare-datatypes ((nat 0)) (((Z) (S (pred nat)))))
(declare-const n nat)

(assert (= n (S (S n))))

(check-sat)
