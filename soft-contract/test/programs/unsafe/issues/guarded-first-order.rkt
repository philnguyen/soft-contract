#lang racket/base

(require racket/contract)

(provide
 (contract-out
  [guarded (((integer? . -> . integer?) . -> . integer?)
            . -> .
            integer?)]))

(define (guarded f)
  (if (= (+ (f (λ (n) 4))
            (f (λ (y) (* y 2))))
         10)
      (if (= (f (λ (m) 0)) -1)
          (f (λ (w)
               (if (= w 2)
                   "BUG"
                   0)))
          0)
      0))
