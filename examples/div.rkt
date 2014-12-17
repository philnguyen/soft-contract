#lang soft-contract

(module div racket
  (provide/contract
   [f ((integer? integer? . -> . integer?) integer? integer? integer? integer? . -> . real?)])
  (define (f g a b c d)
    ;; If you change (g c d) to (g a b), the program is safe
    (/ 1 (- 10 (* (g a b) (g c d))))))
