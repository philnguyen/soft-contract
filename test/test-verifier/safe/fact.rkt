#lang racket
(require soft-contract/fake-contract)

(define (factorial x) 
  (if (zero? x) 
      1
      (* x (factorial (sub1 x)))))

(provide
 (contract-out 
  [factorial (-> (>=/c 0) (>=/c 0))]))
