#lang racket

(define f
  (letrec ([g (λ () g)])
    g))
(define f2 f)
(define f3 f2)
(define c (->i () (_ () (recursive-contract c #:chaperone))))
(define c2 (-> (recursive-contract c2 #:chaperone)))
(define c3 (->i () (_ () c3)))

(provide
 (contract-out
  [f c]
  [f2 c2]
  [f3 c3]))
