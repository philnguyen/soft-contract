(module f racket
  (provide (contract-out [f ((and/c real? (</c 0)) . -> . integer?)]))
  (define (f n)
    (/ 1 (- 100 n))))

#| Z3 does not give a model to this
(declare-const X7 Real)
(declare-const L1 Real)
(declare-const L0 Real)
(assert (= L1 (/ (to_real 1) L0)))
(assert (= L0 (- (to_real 100) X7)))
(assert (not (is_int L1)))
(assert (> (to_real L1) (to_real 0)))
(assert (< (to_real X7) (to_real 0)))
(assert (not (= (to_real L1) (to_real 0))))
(check-sat)
(get-model)
|#
