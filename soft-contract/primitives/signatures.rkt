#lang typed/racket/base

(provide prim-runtime^)

(require typed/racket/unit
         typed/racket/unsafe
         set-extras
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(unsafe-require/typed syntax/id-table
  [#:opaque Parse-Prim-Table free-id-table?]
  [(make-free-id-table make-parse-prim-table) (#:phase (U #f Integer) → Parse-Prim-Table)]
  [(free-id-table-ref parse-prim-table-ref) (∀ (X) Parse-Prim-Table Identifier (→ X) → (U X -prim))]
  [(free-id-table-set! parse-prim-table-set!) (Parse-Prim-Table Identifier -prim → Void)]
  [(free-id-table-count parse-prim-table-count) (Parse-Prim-Table → Index)]
  [(in-free-id-table in-parse-prim-table) (Parse-Prim-Table → (Sequenceof Identifier -prim))]

  [#:opaque Alias-Table #|HACK|# mutable-free-id-table?]
  [(make-free-id-table make-alias-table) (#:phase (U #f Integer) → Alias-Table)]
  [(free-id-table-ref alias-table-ref) (∀ (X) Alias-Table Identifier (→ X) → (U X Identifier))]  
  [(free-id-table-set! alias-table-set!) (Alias-Table Identifier Identifier → Void)]
  [(free-id-table-count alias-table-count) (Alias-Table → Index)]
  [(in-free-id-table in-alias-table) (Alias-Table → (Sequenceof Identifier Identifier))])

(unsafe-provide Parse-Prim-Table
                make-parse-prim-table
                parse-prim-table-ref
                parse-prim-table-set!
                parse-prim-table-count
                in-parse-prim-table

                Alias-Table
                make-alias-table
                alias-table-ref
                alias-table-set!
                alias-table-count
                in-alias-table)

;; TODO: tmp. hack. Signature doesn't need to be this wide.
(define-signature prim-runtime^
  ([make-total-pred : (Index → Symbol → -⟦f⟧)]
   [implement-predicate : (-σ -φ Symbol (Listof -V^) → -V^)]
   [Vs->bs : ((Listof -V) → (Option (Listof Base)))]
   [make-static-listof : (Symbol (→ (Values Boolean -V ℓ)) → -V)]
   [make-listof : (Boolean -V ℓ → -V)]
   [make-static-∀/c : (Symbol Symbol (Listof Symbol) (→ -e) → -V)]
   [make-∀/c : (Symbol (Listof Symbol) -e -ρ → -V)]
   [exec-prim
    : (-H -φ -Σ -⟦k⟧
          ℓ (Intersection Symbol -o)
          #:volatile? Boolean
          #:dom (Listof (Pairof -V ℓ))
          #:rng (Listof -V)
          #:rng-wrap (Option (Listof (Pairof -V ℓ)))
          #:refinements (Listof (List (Listof -V) (Option -V) (Listof -V)))
          #:args (Listof -V)
          → (℘ -ς))]

   [get-weakers : (Symbol → (℘ Symbol))]
   [get-strongers : (Symbol → (℘ Symbol))]
   [get-exclusions : (Symbol → (℘ Symbol))]

   [add-implication! : (Symbol Symbol → Void)]
   [add-exclusion! : (Symbol Symbol → Void)]
   [set-range! : (Symbol Symbol → Void)]
   [update-arity! : (Symbol Arity → Void)]
   [set-partial! : (Symbol Natural → Void)]

   [prim-table : (HashTable Symbol -⟦f⟧)]
   [const-table : Parse-Prim-Table]
   [alias-table : Alias-Table]
   [debug-table : (HashTable Symbol Any)]
   [opq-table : (HashTable Symbol -●)]
   [range-table : (HashTable Symbol Symbol)]
   [arity-table : (HashTable Symbol Arity)]
   [partial-prims : (HashTable Symbol Natural)]

   [add-alias! : (Identifier Identifier → Void)]
   [add-const! : (Identifier -prim → Void)]

   ;; re-exported stuff to avoid confusing dependency in `def`
   [r:Γ⊢oV/handler : ((→ (℘ -ς)) (→ (℘ -ς)) -σ -Γ -o -V * → (℘ -ς))]
   [mk-● : (-h * → -●)]
   [add-seal! : (-Σ Symbol -H -l → -Seal/C)]
   ))
