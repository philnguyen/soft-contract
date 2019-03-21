#lang typed/racket/base

(provide (all-defined-out))

(: vector-ormap (∀ (α β) (α → β) (Vectorof α) → (U #f β)))
(define (vector-ormap p? xs)
  (for/or : (Option β) ([x (in-vector xs)])
    (p? x)))

(: vector-andmap (∀ (α β) (α → β) (Vectorof α) → (U #t β)))
(define (vector-andmap p? xs)
  (for/fold ([acc : (U #t β) #t]) ([x (in-vector xs)] #:break (not acc))
    (p? x)))
