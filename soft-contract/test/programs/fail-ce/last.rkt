#lang racket
(require soft-contract/fake-contract)

(define (Y f)
  (λ (y)
    (((λ (x) (f (λ (z) ((x x) z))))
      (λ (x) (f (λ (z) ((x x) z)))))
     y)))

(define (last l)
  ((Y (λ (f)
        (λ (x)
          (if (empty? (cdr x)) (car x) (f (cdr x))))))
   l))

(provide/contract [last (#|HERE|#(listof any/c) . -> . any/c)])
