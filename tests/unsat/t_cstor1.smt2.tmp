
; test for constructors
; :status unsat

(declare-sort nat 0)
(declare-cstor zero () nat)
(declare-cstor succ (nat) nat)

(declare-fun n0 () nat)
(declare-fun n1 () nat)
(declare-fun n2 () nat)

(assert (= n0 (succ (succ (succ (succ zero))))))
(assert (= n1 (succ (succ n2))))
(assert (not (= n1 (succ (succ (succ (succ zero)))))))

; (check-sat) ; sat

(assert (= n2 (succ (succ zero))))

(check-sat) ; unsat

(exit)
