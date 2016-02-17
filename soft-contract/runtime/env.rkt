#lang typed/racket/base

(provide (all-defined-out))

(require "addr.rkt")

(define-type -ρ (HashTable Symbol -α))
(define ⊥ρ : -ρ (hasheq))
(define ρ@ : (-ρ Symbol → -α) hash-ref)
(define ρ+ : (-ρ Symbol -α → -ρ) hash-set)

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) ρ]) `(,x ↦ ,(show-α α))))
