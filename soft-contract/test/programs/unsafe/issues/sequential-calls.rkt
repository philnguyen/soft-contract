#lang racket/base
(require racket/contract)

(provide
 (contract-out
  [sequential (((integer? . -> . integer?) . -> . integer?)
               . -> .
               integer?)]))

(define (ω) (ω))

(define (sequential f)
  (let* ([i (f (λ (n) (if (= n 7) 73 (ω))))]
         [j (f (λ (n)
                 (cond
                   [(= n 7) 64]
                   [(= n 31) "BUG"]
                   [else 73])))])
    0))
