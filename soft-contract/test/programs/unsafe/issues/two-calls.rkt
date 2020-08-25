#lang racket/base

(require racket/contract)

(define (equals m)
  (λ (n) (if (= n m) 0 1)))

(define (twocalls F)
  (let* ([i (F (equals 2))]
         [j (F (equals 30))]
         [k (F (equals 7))])
    (if (and (= i 12) (= j 5) (= k -2))
        "BUG"
        0)))

(provide
 (contract-out
  [twocalls (((integer? . -> . integer?) . -> . integer?)
             . -> .
             integer?)]))
