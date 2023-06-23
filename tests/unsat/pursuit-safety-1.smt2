(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
SAL benchmark suite.  Created at SRI by Bruno Dutertre, John Rushby, Maria
Sorea, and Leonardo de Moura.  Contact demoura@csl.sri.com for more
information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun x_0 () Bool)
(declare-fun x_1 () Bool)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Bool)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Bool)
(declare-fun x_9 () Real)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Real)
(assert (let ((?v_3 (= 10 40)) (?v_27 (+ 10 (* x_2 6))) (?v_4 (= 10 0)) (?v_2 (= 20 40)) (?v_6 (= 20 0)) (?v_13 (< (+ (- (* 10 5) (* 20 6)) 40) 0)) (?v_30 (+ 20 (* x_2 5))) (?v_28 (+ 2 x_2)) (?v_10 (= 2 2)) (?v_7 (= x_3 20)) (?v_23 (not x_0))) (let ((?v_29 (and ?v_23 x_1)) (?v_15 (not x_1))) (let ((?v_18 (and x_0 ?v_15)) (?v_5 (and (= x_4 x_0) (= x_5 x_1))) (?v_8 (= x_6 10)) (?v_0 (and ?v_23 ?v_15)) (?v_14 (= x_7 0)) (?v_21 (not x_4))) (let ((?v_17 (and ?v_21 x_5)) (?v_1 (not x_8)) (?v_12 (not ?v_2)) (?v_9 (= x_7 2)) (?v_26 (or ?v_23 x_1)) (?v_11 (not ?v_6)) (?v_25 (or x_0 x_1)) (?v_20 (not ?v_13)) (?v_16 (or ?v_6 ?v_2)) (?v_19 (= x_6 (ite ?v_3 0 (ite ?v_4 40 10)))) (?v_24 (and (and (<= ?v_28 2) (not (< ?v_30 0))) (<= ?v_27 40))) (?v_22 (not x_5))) (and (and (and (and (and (and (and (and (and (<= x_10 1) (>= x_10 0)) ?v_0) (not (< x_9 0))) (= x_10 (ite x_8 0 1))) (not (< x_11 0))) (or (or (or (or (or (or (or (or (and (and (and (and (and (and (and (and (and (and (= x_12 0) ?v_1) ?v_0) ?v_10) ?v_11) ?v_12) ?v_13) ?v_14) ?v_7) ?v_8) ?v_5) (and (and (and (and (and (and (and (= x_12 1) ?v_1) ?v_0) (or (or ?v_2 ?v_4) ?v_3)) (= x_3 (ite ?v_2 0 20))) ?v_19) ?v_5) ?v_9)) (and (and (and (and (and (and (and (= x_12 2) ?v_1) ?v_0) ?v_16) ?v_17) ?v_7) ?v_8) ?v_9)) (and (and (and (and (and (and (and (and (and (and (and (= x_12 3) ?v_1) ?v_0) ?v_10) ?v_11) ?v_12) ?v_20) x_4) ?v_22) ?v_14) ?v_7) ?v_8)) (and (and (and (and (and (and (and (= x_12 4) ?v_1) ?v_18) ?v_16) ?v_17) ?v_7) ?v_8) ?v_9)) (and (and (and (and (and (and (and (= x_12 5) ?v_1) ?v_18) (or (or ?v_6 ?v_4) ?v_3)) (= x_3 (ite ?v_6 40 20))) ?v_19) ?v_5) ?v_9)) (and (and (and (and (and (and (and (and (and (and (= x_12 6) ?v_1) ?v_18) ?v_10) ?v_11) ?v_12) ?v_20) ?v_14) ?v_7) ?v_8) ?v_5)) (and (and (and (and (and (and (and (and (and (and (and (= x_12 7) ?v_1) ?v_18) ?v_10) ?v_11) ?v_12) ?v_13) ?v_21) ?v_22) ?v_14) ?v_7) ?v_8)) (and (and (and (and (and (and (and (and (and (= x_12 8) x_8) (not (< x_2 0))) (or ?v_25 ?v_24)) (or ?v_26 ?v_24)) (or (and ?v_25 ?v_26) (and (not (< (* x_11 2) (- (* 10 2) x_2))) (<= x_11 ?v_27)))) (= x_7 (ite ?v_29 2 ?v_28))) (= x_3 (ite ?v_29 20 ?v_30))) (= x_6 (ite ?v_29 10 x_11))) ?v_5))) (or (= x_3 x_6) (= 20 10))) (or ?v_15 ?v_23)) (or ?v_22 ?v_21)))))))
(check-sat)
(exit)
