#lang racket

(provide x f?)
(require racket/bool)

(define x 42)

(define f? false?)

(require racket/match)

(define g
  (λ (z) (let-values ([(a b c) (values 1 2 3)]
                      [(m n) (values 42 43)])
           (printf "hi ~a" b))))
