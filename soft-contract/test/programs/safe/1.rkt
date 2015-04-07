#lang racket
(require racket/bool soft-contract/fake-contract racket/list)

(define x 42)

(define f? false?)

(define g
  (λ (z) (let-values ([(a b c) (values 1 2 3)]
                      [(m n) (values 42 43)])
           (list a b c m n))))

(provide x f?)
