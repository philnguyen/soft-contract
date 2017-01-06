#lang typed/racket/base

(provide (all-defined-out)
         debug-table)

(require "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt"
         (only-in "../primitives/def-prim-runtime.rkt"
                  debug-table))

(define-type -⟦f⟧ (-l -$ -ℒ (Listof -W¹) -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))

(define ext-table : (HashTable Symbol -⟦f⟧) (make-hasheq))

(: get-ext : Symbol → (Option -⟦f⟧))
(define (get-ext o) (hash-ref ext-table o #f))