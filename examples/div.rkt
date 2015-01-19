#lang racket
(require soft-contract/fake-contract)

(define (f g a b c d)
  ;; If you change (g c d) to (g a b), the program is safe
  (/ 1 (- 10 (* (g a b) (g c d)))))

(provide
   (contract-out
    [f ((integer? integer? . -> . integer?) integer? integer? integer? integer? . -> . real?)]))
