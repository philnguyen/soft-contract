(module f racket
  (provide/contract [f (integer? . -> . integer?)])
  (define (f n)
    (/ 1 (+ 1 (* n n)))))

#| Z3 cannot give a model to this:
(declare-const X7 Int)
(declare-const L2 Real)
(declare-const L1 Int)
(declare-const L0 Int)
(assert (= L2 (/ (to_real 1) (to_real L1))))
(assert (not (is_int L2)))
(assert (= L1 (+ 1 L0)))
(assert (> (to_real L2) 0))
(assert (= L0 (* X7 X7)))
(assert (not (= (to_real L2) 0)))
(assert (>= L1 0))
(check-sat)
(get-model)
|#
