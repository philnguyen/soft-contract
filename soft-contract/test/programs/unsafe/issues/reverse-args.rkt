#lang racket/base

(require racket/contract)

(provide
 (contract-out
  [reversed (((integer? . -> . integer?)
              . -> .
              (integer? . -> . integer?))
             . -> .
             integer?)]))

(define (ω) (ω))

(define (reversed f)
  (let* ([n1 ((f (λ (n) (if (= n 0) 10 (ω)))) 0)]
         [n2 ((f (λ (n) (if (= n 0) 23 (ω)))) 0)]
         [n3 ((f (λ (m) (if (= m 1) 37 (ω)))) 1)]
         [n4 ((f (λ (m) (if (= m 1) 41 (ω)))) 1)])
    (if (and (= n1 12)
             (= n2 34)
             (= n3 56)
             (= n4 78))
        "BUG"
        0)))
