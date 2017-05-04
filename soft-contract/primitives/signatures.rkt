#lang typed/racket/base

(provide prim-runtime^)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/main.rkt")

;; TODO: tmp. hack. Signature doesn't need to be this wide.
(define-signature prim-runtime^
  ([add-implication! : (Symbol Symbol → Void)]
   [add-exclusion! : (Symbol Symbol → Void)]
   [set-range! : (Symbol Symbol → Void)]
   [update-arity! : (Symbol Arity → Void)]
   [set-partial! : (Symbol Natural → Void)]
   
   [make-total-pred : (Index → Symbol → -⟦o⟧)]
   [implement-predicate : (-M -σ -Γ Symbol (Listof -W¹) → (℘ -ΓA))]

   [prim-table : (HashTable Symbol -⟦o⟧)]
   [debug-table : (HashTable Symbol Any)]
   [alias-table : (HashTable Symbol Symbol)]
   [opq-table : (HashTable Symbol -●)]))
