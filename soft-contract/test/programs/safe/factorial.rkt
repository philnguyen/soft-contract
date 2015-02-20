#lang racket
(require soft-contract/fake-contract)

(define (factorial n)
  (if (zero? n) 1 (* n (factorial (sub1 n)))))

(provide/contract
 [factorial (integer? . -> . integer?)])
