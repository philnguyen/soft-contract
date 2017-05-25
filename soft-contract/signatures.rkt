#lang typed/racket/base

(provide verifier^ reduction^ parser^ prims^ proof-system^ widening^ for-gc^)

(require typed/racket/unit
         set-extras
         "ast/main.rkt"
         "runtime/signatures.rkt")

(define-signature verifier^
  ([run-files : ((Listof Path-String) → (Values (℘ -ΓA) -Σ))]
   [havoc-files : ((Listof Path-String) → (Values (℘ -ΓA) -Σ))]
   [havoc-last-file : ((Listof Path-String) → (Values (℘ -ΓA) -Σ))]
   [run-e : (-e → (Values (℘ -ΓA) -Σ))]))

(define-signature reduction^
  ([run : (-⟦e⟧ → (Values (℘ -ΓA) -Σ))]))

(define-signature parser^ ; TODO
  ([parse-files : ((Listof Path-String) → (Listof -module))]))

(define-signature prims^ ; TODO
  ([get-prim : (Symbol → (Option -Prim))]
   [o⇒o : (Symbol Symbol → -R)]
   [get-conservative-range : (Symbol → Symbol)]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [prim-arity : (Symbol → Arity)]
   [extract-list-content : (-σ -St → (℘ -V))]
   [parse-prim : (Identifier → (Option -prim))]))

(define-signature proof-system^
  ([MΓ⊢V∈C : (-M -σ -Γ -W¹ -W¹ → -R)]
   [MΓ⊢oW : (-M -σ -Γ -o -W¹ * → -R)]
   [Γ+/-V : (-M -Γ -V -?t → (Values (Option -Γ) (Option -Γ)))]
   [MΓ+/-oW : (-M -σ -Γ -o -W¹ * → (Values (Option -Γ) (Option -Γ)))]
   [plausible-index? : (-M -σ -Γ -W¹ Natural → Boolean)]
   [MΓ+/-oW/handler : (∀ (X) (-Γ → (℘ X)) (-Γ → (℘ X)) -M -σ -Γ -o -W¹ * → (℘ X))]
   [MΓ⊢oW/handler : (∀ (X) (→ (℘ X)) (→ (℘ X)) -M -σ -Γ -o -W¹ * → (℘ X))]
   [p∋Vs/handler : (∀ (X) (→ (℘ X)) (→ (℘ X)) -σ -o -V * → (℘ X))]))

;; FIXME: least coherent signature ever.
;; Could have named it "misc"...
(define-signature widening^
  ([σ⊕! : ([-Σ -Γ ⟪α⟫ -W¹] [#:mutating? Boolean] . ->* . Void)]
   [σ⊕V! : ([-Σ ⟪α⟫ -V] [#:mutating? Boolean] . ->* . Void)]
   [M⊕! : (-Σ -αₖ (℘ -t) -A → Void)]
   [σₖ⊕! : (-Σ -αₖ -κ → Void)]
   [Vs⊕ : (-σ (℘ -V) -V → (℘ -V))]
   [Γ+ : (-Γ -?t * → -Γ)]
   [V+ : (-σ -V (U -V -h (℘ -h)) → -V)]
   [predicates-of-W : (-σ -Γ -W¹ → (U (℘ -h) -⟦e⟧))]
   [inv-caller->callee : (-σ (℘ Symbol) -formals (Listof -W¹) -Γ -Γ → -Γ)]
   [inv-callee->caller : (-σ (℘ Symbol) -formals (Listof -?t) -Γ -Γ → (Option -Γ))]
   [add-leak! : (-Σ -V → Void)]
   [alloc-init-args! : (-Σ -Γ -ρ -⟪ℋ⟫ -?t (Listof Symbol) (Listof -W¹) → -ρ)]
   [alloc-rest-args! : ([-Σ -Γ -⟪ℋ⟫ -ℒ (Listof -W¹)] [#:end -V] . ->* . -V)]
   [estimate-list-lengths : (-σ -V → (℘ (U #f Arity)))]
   [unalloc : (-σ -V → (℘ (Option (Listof -V))))]
   [unalloc-prefix : (-σ -V Natural → (℘ (Pairof (Listof -V) -V)))]))

(define-signature for-gc^
  ([add-⟦k⟧-roots! : (-⟦k⟧ (℘ ⟪α⟫) → Void)]
   [⟦k⟧->roots : (-⟦k⟧ → (℘ ⟪α⟫))]
   [set-⟦k⟧->αₖ! : (-⟦k⟧ -αₖ → Void)]
   [⟦k⟧->αₖ : (-⟦k⟧ → -αₖ)]
   [V->⟪α⟫s : (-V → (℘ ⟪α⟫))]
   [ρ->⟪α⟫s : (-ρ → (℘ ⟪α⟫))]
   [span-σ : ((HashTable ⟪α⟫ (℘ -V)) (℘ ⟪α⟫) → (HashTable ⟪α⟫ (℘ -V)))]
   [t->αₖs : (-?t → (℘ -αₖ))]
   [Γ->αₖs : (-Γ → (℘ -αₖ))]
   [ΓA->αₖs : (-ΓA → (℘ -αₖ))]
   [αₖ->⟪α⟫s : (-αₖ (HashTable -αₖ (℘ -κ)) → (℘ ⟪α⟫))]
   [span-M : ((HashTable -αₖ (℘ -ΓA)) (℘ -αₖ) → (HashTable -αₖ (℘ -ΓA)))]
   [->⟪α⟫s : ((Rec X (U ⟪α⟫ -V -W¹ -W -ρ (-var X) (Listof X) (℘ X))) → (℘ ⟪α⟫))]
   [σ-equal?/spanning-root : (-σ -σ (℘ ⟪α⟫) → Boolean)]))
