#lang typed/racket/base

(provide verifier^ reduction^ parser^ prims^ proof-system^ widening^ for-gc^ lib^ debugging^)

(require typed/racket/unit
         set-extras
         "ast/signatures.rkt"
         "runtime/signatures.rkt")

(define-signature verifier^
  ([run-files : ((Listof Path-String) → (Values (℘ -ΓA) -Σ))]
   [havoc-files : ((Listof Path-String) → (Values (℘ -ΓA) -Σ))]
   [havoc-files/profile : ([(Listof Path-String)] [#:delay Positive-Real] . ->* . (Values (℘ -ΓA) -Σ))]
   [havoc-last-file : ((Listof Path-String) → (Values (℘ -ΓA) -Σ))]
   [run-e : (-e → (Values (℘ -ΓA) -Σ))]
   [debug-iter? : (Parameterof Boolean)]
   [debug-trace? : (Parameterof Boolean)]
   [max-steps : (Parameterof (Option Natural))]))

(define-signature lib^
  ([verify : (Syntax (HashTable Symbol Syntax) → Any)]))

(define-signature reduction^
  ([run : (-⟦e⟧ → (Values (℘ -ΓA) -Σ))]))

(define-signature parser^ ; TODO
  ([parse-files : ((Listof Path-String) → (Listof -module))]
   [parse-module : (Syntax → -module)]
   [parse-expr : (Syntax → -e)]
   [canonicalize-path : (Path-String → Path-String)]))

(define-signature prims^ ; TODO
  ([get-prim : (Symbol → -⟦f⟧)]
   [o⇒o : (Symbol Symbol → -R)]
   [get-conservative-range : (Symbol → Symbol)]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [prim-arity : (Symbol → Arity)]
   [parse-prim : (Identifier → (Option -prim))]))

(define-signature proof-system^
  ([Γ⊢V∈C : (-σ -Γ -W¹ -W¹ → -R)]
   [Γ⊢oW : (-σ -Γ -o -W¹ * → -R)]
   [Γ+/-V : (-Γ -V -?t → (Values (Option -Γ) (Option -Γ)))]
   [Γ+/-oW : (-σ -Γ -o -W¹ * → (Values (Option -Γ) (Option -Γ)))]
   [plausible-index? : (-σ -Γ -W¹ Natural → Boolean)]
   [Γ+/-oW/handler : (∀ (X) (-Γ → (℘ X)) (-Γ → (℘ X)) -σ -Γ -o -W¹ * → (℘ X))]
   [Γ⊢oW/handler : (∀ (X) (→ (℘ X)) (→ (℘ X)) -σ -Γ -o -W¹ * → (℘ X))]
   [p∋Vs/handler : (∀ (X) (→ (℘ X)) (→ (℘ X)) -σ -o -V * → (℘ X))]))

;; FIXME: least coherent signature ever.
;; Could have named it "misc"...
(define-signature widening^
  ([σ⊕! : (-Σ -Γ ⟪α⟫ -W¹ → Void)]
   [σ⊕V! : (-Σ ⟪α⟫ -V → Void)]
   [σ⊕Vs! : (-Σ ⟪α⟫ (℘ -V) → Void)]
   [σ-copy! : (-Σ ⟪α⟫ ⟪α⟫ → Void)]
   [σₖ+! : (-Σ -αₖ -κ → -αₖ)]
   [Vs⊕ : (-σ (℘ -V) (U -V (℘ -V)) → (℘ -V))]
   [ps⊕ : ((℘ -h) (℘ -h) → (℘ -h))]
   [σₐ⊕! : (-Σ -αₖ -ΓA → Void)]
   [Γ+ : (-Γ -?t * → -Γ)]
   [V+ : (-σ -V (U -V -h (℘ -h)) → -V)]
   [add-leak! : (-l -Σ -V → Void)]
   [bind-args! : (-Σ -$ -Γ -ρ -H (Listof Symbol) (Listof -W¹) Boolean
                     → (Values -ρ -$ (Immutable-HashTable Symbol -t)))]
   [alloc-init-args! : (-Σ -$ -Γ -ρ -H (Listof Symbol) (Listof -W¹) Boolean
                           → (Values -ρ -$ (Immutable-HashTable Symbol -t)))]
   [alloc-rest-args! : ([-Σ -Γ -H ℓ (Listof -W¹)] [#:end -V] . ->* . -V)]
   [estimate-list-lengths : (-σ -V → (℘ (U #f Arity)))]
   [unalloc : (-σ -V → (℘ (Option (Listof -V))))]
   [unalloc-prefix : (-σ -V Natural → (℘ (Pairof (Listof -V) -V)))]
   [copy-Γ : ((℘ (U Symbol ℓ)) -Γ -Γ → -Γ)]))

(define-signature for-gc^
  ([add-⟦k⟧-roots! : (-⟦k⟧ (℘ ⟪α⟫) → Void)]
   [⟦k⟧->roots : (-⟦k⟧ → (℘ ⟪α⟫))]
   [set-⟦k⟧->αₖ! : (-⟦k⟧ -αₖ → Void)]
   [⟦k⟧->αₖ : (-⟦k⟧ → -αₖ)]
   [V->⟪α⟫s : (-V → (℘ ⟪α⟫))]
   [ρ->⟪α⟫s : (-ρ → (℘ ⟪α⟫))]
   [αₖ->⟪α⟫s : (-αₖ -σₖ → (℘ ⟪α⟫))]
   [⟦k⟧->⟪α⟫s : (-⟦k⟧ -σₖ → (℘ ⟪α⟫))]
   [->⟪α⟫s : ((Rec X (U ⟪α⟫ -V -W¹ -W -ρ (-var X) (Listof X) (℘ X))) → (℘ ⟪α⟫))]
   [σ-equal?/spanning-root : (-σ -σ (℘ ⟪α⟫) → Boolean)]
   [bound-vars : (-⟦e⟧ → (℘ Symbol))]
   [set-bound-vars! : (-⟦e⟧ (℘ Symbol) → Void)]
   [gc-$ : (-$ -σ (℘ ⟪α⟫) → -$)]))

(define-signature debugging^
  ([print-Σ-stat : (-Σ → Void)]
   [print-large-sets : ([-Σ] [#:val-min Index #:kont-min Index #:ctx-min Index] . ->* . Void)]))
