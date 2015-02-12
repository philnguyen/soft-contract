(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (expt 2 n)))

#| Z3 does not give a model to this
(declare-const X7 Int)
(declare-const L0 Real)
(assert (not (is_int L0)))
(assert (= L0 (expt 2 (to_real X7))))
(check-sat)
(get-model)
|#
