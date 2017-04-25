#lang racket
(require soft-contract/fake-contract)

(define (fib n)
  (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))

(provide/contract
 [fib (integer? . -> . integer?)])
