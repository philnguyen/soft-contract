#lang racket
(require soft-contract/fake-contract)

(define f
  (match-lambda
    [(cons x y) #:when (> x 4) (add1 x)]
    [(? number? z) (add1 z)]
    [(? string? s) (string-length s)]
    [(vector n s) (string-length s)]
    [(vector _ _ _) #|DEAD|# (add1 "")]))

(provide
 (contract-out
  [f ((or/c (or/c string? number?)
            (or/c (cons/c (>/c 6) any/c)
                  (vector/c integer? string?))) . -> . number?)]))
