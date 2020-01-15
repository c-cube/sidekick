
(set-info :status unsat)
(declare-datatypes ((nat 0)) (((Z) (S (pred nat)))))
(declare-const p Bool)
(declare-const n nat)
(declare-const n_t nat)
(declare-const n_f nat)

(assert (= n_t (S n)))
(assert (= n_f (S (S n))))
(assert (=> p (= n (S n_t))))
(assert (=> (not p) (= n (S n_f))))

(check-sat)
