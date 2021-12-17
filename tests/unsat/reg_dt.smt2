
; expect: unsat

(set-logic QF_UFDT)
(declare-datatypes
  ((foo 0))
  (((A) (B) (C))))

(declare-datatypes
  ((tup 0))
  (((mk_tup (x foo) (y foo)))))

(declare-datatypes
  ((bar 0))
  (((mk_bar (b1 tup) (b2 Bool)))))

(declare-fun x0 () bar)
(declare-fun f (bar) bar)

(assert
 (= (f x0)
    (mk_bar (b1 x0) (not (b2 x0)))))

(assert
 (let ((x1 (f x0)))
 (= (f x1)
    (mk_bar (b1 x1) (not (b2 x1))))))

; the goal: f(f(x0))=x0
(assert (not (= x0 (f (f x0)))))

(check-sat)


