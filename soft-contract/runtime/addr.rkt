#lang typed/racket/base

(provide (all-defined-out))

(require "../ast/definition.rkt" "definition.rkt")

(: alloc-fields : -ℓ -𝒞 Natural → (Listof -α.fld))
(define (alloc-fields ℓ 𝒞 n)
  (for/list ([i : Natural n])
    (-α.fld ℓ 𝒞 i)))
