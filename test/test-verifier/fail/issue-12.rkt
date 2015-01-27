#lang racket
(require soft-contract/fake-contract)

(define (f n)
  (if (= n 100)
      5
      (/ 1 (- 100 n))))

(provide/contract
 [f (integer? . -> . integer?)])
