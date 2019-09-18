#lang racket/base

(require racket/contract
         (submod (lib "typed-racket/private/type-contract.rkt") predicates))
(define g8 real?)
(define g9 (or/c g8))
(define generated-contract3 (-> g9 (values g9)))
(define generated-contract4 (-> g9 g9 (values g9)))
(define generated-contract5 (-> g9 g9 (values g9)))
(define generated-contract6 (-> (and/c real? nonnegative?) (values g9)))
(define generated-contract7 (-> g9 (values g9)))

(define (min x y) (if (<= x y) x y))

(define (max x y) (if (>= x y) x y))

(define (abs x) (if (>= x 0) x (- 0 x)))

(define (sqr x) (* x x))

(define (msqrt x) (sqrt x))
(provide sqrt)
(provide (contract-out (msqrt generated-contract6))
         (contract-out (sqr generated-contract7))
         (contract-out (abs generated-contract3))
         (contract-out (max generated-contract4))
         (contract-out (min generated-contract5)))
