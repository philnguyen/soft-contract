#lang typed/racket/base

(provide prim-runtime^)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/main.rkt")

;; TODO: tmp. hack. Signature doesn't need to be this wide.
(define-signature prim-runtime^
  ([⊢?/quick : (-R -σ (℘ -t) -o -W¹ * → Boolean)]
   [make-total-pred : (Index → Symbol → -⟦o⟧)]
   [implement-predicate : (-M -σ -Γ Symbol (Listof -W¹) → (℘ -ΓA))]
   [ts->bs : ((Listof -?t) → (Option (Listof Base)))]
   [extract-list-content : (-σ -St → (℘ -V))]
   [unchecked-ac : (-σ -Γ -st-ac -W¹ → (℘ -W¹))]
   [arity-check/handler : (∀ (X) (-Γ → (℘ X)) (-Γ → (℘ X)) -Γ -W¹ Arity → (℘ X))]

   [get-weakers : (Symbol → (℘ Symbol))]
   [get-strongers : (Symbol → (℘ Symbol))]
   [get-exclusions : (Symbol → (℘ Symbol))]

   [add-implication! : (Symbol Symbol → Void)]
   [add-exclusion! : (Symbol Symbol → Void)]
   [set-range! : (Symbol Symbol → Void)]
   [update-arity! : (Symbol Arity → Void)]
   [set-partial! : (Symbol Natural → Void)]

   [prim-table : (HashTable Symbol -⟦o⟧)]
   [const-table : (HashTable Symbol -prim)]
   [debug-table : (HashTable Symbol Any)]
   [alias-table : (HashTable Symbol Symbol)]
   [opq-table : (HashTable Symbol -●)]
   [range-table : (HashTable Symbol Symbol)]
   [arity-table : (HashTable Symbol Arity)]))
