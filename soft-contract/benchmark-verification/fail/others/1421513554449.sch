(module f racket
  (provide (contract-out [f ((and/c integer? (</c 100)) . -> . integer?)]))
  (define (f n)
    (/ 1 (- 100 n))))

;; Z3 does not give a model to this
; (declare-const X7 Int)
; (declare-const L1 Real)
; (declare-const L0 Int)
; (assert (< X7 100))
; (assert (= L1 (/ (to_real 1) (to_real L0))))
; (assert (not (is_int L1)))
; (assert (> (to_real L1) (to_real 0)))
; (assert (= L0 (- 100 X7)))
; (assert (not (= (to_real L1) (to_real 0))))
; (check-sat)
; (get-model)

