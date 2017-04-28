#lang typed/racket/base

(provide verifier^ reduction^ parser^ prims^ exts^ proof-system^ widening^)

(require typed/racket/unit
         set-extras
         "ast/main.rkt"
         "runtime/main.rkt")

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
  ([get-prim : (Symbol → (Option -⟦o⟧))]
   [alias-table : (HashTable Symbol Symbol)]
   [alias-internal-table : (HashTable Symbol (U -st-mk -st-p -st-ac -st-mut))]
   [const-table : (HashTable Symbol -b)]
   [prim-table : (HashTable Symbol -⟦o⟧)]
   [opq-table : (HashTable Symbol -●)]
   [vec-len : (-σ -Γ -W¹ → -W¹)]))

(define-signature exts^ ; TODO
  ([get-ext : (Symbol → (Option -⟦f⟧))]))

(define-signature proof-system^
  ([MΓ⊢V∈C : (-M -σ -Γ -W¹ -W¹ → -R)]
   [MΓ⊢oW : (-M -σ -Γ -o -W¹ * → -R)]
   [Γ+/-V : (-M -Γ -V -?t → (Values (Option -Γ) (Option -Γ)))]
   [MΓ+/-oW : (-M -σ -Γ -o -W¹ * → (Values (Option -Γ) (Option -Γ)))]
   [plausible-index? : (-M -σ -Γ -W¹ Natural → Boolean)]
   [V-arity : (-V → (Option Arity))]
   [Γ⊢t : ((℘ -t) -?t → -R)]
   [plausible-V-t? : ((℘ -t) -V -?t → Boolean)]
   [sat-one-of : (-V (Listof Base) → -R)]
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
   [Γ+ : (-Γ -?t * → -Γ)]
   [V+ : (-σ -V (U -V -h (℘ -h)) → -V)]
   [predicates-of-W : (-σ -Γ -W¹ → (U (℘ -h) -⟦e⟧))]
   [inv-caller->callee : (-σ (℘ Symbol) -formals (Listof -W¹) -Γ -Γ → -Γ)]
   [inv-callee->caller : (-σ (℘ Symbol) -formals (Listof -?t) -Γ -Γ → (Option -Γ))]
   [extract-list-content : (-σ -St → (℘ -V))]
   [add-leak! : (-Σ -V → Void)]))
