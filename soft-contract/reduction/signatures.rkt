#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         bnf
         set-extras
         "../utils/list.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(define-substructs K
  [K:Rt αₖ]
  [K:Ap (Listof V^) (Listof ⟦E⟧) Ρ ℓ K]
  [K:Set! α K]
  [K:Let ℓ (Listof Symbol) (Assoc (Listof Symbol) ⟦E⟧) (Assoc Symbol V^) ⟦E⟧ Ρ K]
  [K:Letrec ℓ (Listof Symbol) (Assoc (Listof Symbol) ⟦E⟧) ⟦E⟧ Ρ K]
  [K:If -l ⟦E⟧ ⟦E⟧ Ρ K]
  [K:Bgn (Listof ⟦E⟧) Ρ K]
  [K:Bgn0:V (Listof ⟦E⟧) Ρ K]
  [K:Bgn0:E (Listof V^) (Listof ⟦E⟧) Ρ K]
  [K:Mon:C Ctx (U (Pairof ⟦E⟧ Ρ) V^) K]
  [K:Mon:V Ctx (U (Pairof ⟦E⟧ Ρ) V^) K]
  [K:Mon*:C Ctx (U (Listof αℓ) 'any) K]
  [K:Mon* Ctx (Listof V^) (Listof V^) (Listof ℓ) (Listof V^) K]
  [K:Μ/C Symbol K]
  [K:==>:Dom (Listof V^) (Listof ⟦E⟧) (Option ⟦E⟧) ⟦E⟧ Ρ ℓ K]
  [K:==>:Rst (Listof V^) ⟦E⟧ Ρ ℓ K]
  [K:==>:Rng (Listof V^) (Option V^) ℓ K]
  [K:==>i Ρ (Listof Dom) (Pairof Symbol ℓ) (Listof ⟦dom⟧) K]
  [K:Struct/C ℓ -𝒾 (Listof V^) (Listof ⟦E⟧) Ρ K]
  [K:Def -l (Listof α) K]
  [K:Dec ℓ -𝒾 K]
  [K.Hv HV-Tag K]
  ;; Specific helpers
  [K:Wrap-St St/C Ctx K]
  [K:Mon-Or/C Ctx V^ V^ V^ K]
  [K:Mk-Wrap-Vect (U Vect/C Vectof) Ctx K]
  [K:If:Flat/C V^ Blm K]
  [K:Fc-And/C -l ℓ V^ V^ K]
  [K:Fc-Or/C -l ℓ V^ V^ V^ K]
  [K:Fc-Not/C V^ K]
  [K:Fc-Struct/C -l ℓ -𝒾 (Listof V^) (Listof ⟦E⟧) Ρ K]
  [K:Fc:V -l ℓ ⟦E⟧ Ρ K]
  [K:RestoreCtx H K]
  [K:Hash-Set-Inner ℓ α K]
  [K:Wrap-Hash Hash/C Ctx K]
  [K:Set-Add-Inner ℓ α K]
  [K:Wrap-Set Set/C Ctx K]
  [K:Maybe-Havoc-Prim-Args ℓ Symbol K]
  [K:Make-Prim-Range Ctx (Option (Listof αℓ)) (Listof V^) (Listof (List (Listof V) (Option V) (Listof V))) K]
  [K:Implement-Predicate Symbol K]
  [K:Absurd K])

(define-substructs -α
  (-α:top -𝒾)
  (-α:wrp -𝒾)
  
  ; for binding
  (-α:x Symbol H)
  ; for struct field
  (-α:fld -𝒾 ℓ H Index)
  ; for Cons/varargs
  ; idx prevents infinite list
  (-α:var-car ℓ H (Option Natural))
  (-α:var-cdr ℓ H (Option Natural))

  ;; for wrapped mutable struct
  (-α:st -𝒾 Ctx H)

  ;; for vector indices
  (-α:idx ℓ H Natural)
  
  ;; for vector^ content
  (-α:vct ℓ H)

  ;; for hash^ content
  (-α:hash:key ℓ H)
  (-α:hash:val ℓ H)

  ;; for set^ content
  (-α:set:elem ℓ H)

  ;; for wrapped vector
  (-α:unvct Ctx H)

  ;; for wrapped hash
  (-α:unhsh Ctx H)

  ;; for wrapped set
  (-α:unset Ctx H)

  ;; for contract components
  (-α:and/c:l ℓ H)
  (-α:and/c:r ℓ H)
  (-α:or/c:l ℓ H)
  (-α:or/c:r ℓ H)
  (-α:not/c ℓ H)
  (-α:x/c Symbol H)
  (-α:vect/c ℓ H Natural)
  (-α:vectof ℓ H)
  (-α:hash/c:key ℓ H)
  (-α:hash/c:val ℓ H)
  (-α:set/c:elem ℓ H)
  (-α:struct/c -𝒾 ℓ H Natural)
  (-α:dom ℓ H Natural)
  (-α:rst ℓ H)
  (-α:rng ℓ H Natural)

  ;; for wrapped function
  (-α:fn Ctx H)

  ;; For values wrapped in seals
  (-α:sealed Symbol H) ; points to wrapped objects

  ;; HACK
  (-α:hv HV-Tag)
  (-α:mon-x/c Symbol H -l)
  (-α:fc-x/c Symbol H))

(define-signature compile^
  ([↓ₚ : ((Listof -module) -e → ⟦E⟧)]
   [↓ₘ : (-module → ⟦E⟧)]
   [↓ₑ : (-l -e → ⟦E⟧)]
   [↓ₓ : (Symbol ℓ → ⟦E⟧)]
   [mk-V : (V → ⟦E⟧)]
   [mk-A : (A → ⟦E⟧)]
   [mk--> : (ℓ (-maybe-var ⟦E⟧) ⟦E⟧ → ⟦E⟧)]
   [mk-->i : ((Listof ⟦dom⟧) ⟦dom⟧ → ⟦E⟧)]
   [mk-app : (ℓ ⟦E⟧ (Listof ⟦E⟧) → ⟦E⟧)]
   [mk-mon : (Ctx ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-fc : (-l ℓ ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-let* : (ℓ (Listof (Pairof Symbol ⟦E⟧)) ⟦E⟧ → ⟦E⟧)]
   [mk-wrapped : (Prox/C Ctx α V^ → ⟦E⟧)]
   [split-⟦dom⟧s : (Ρ (Listof ⟦dom⟧) → (Values (Listof Dom) (Listof ⟦dom⟧)))]
   ))

(define-signature alloc^
  ([mutable? : (α → Boolean)]))

(define-signature widen^
  ([⊔ₐ! : (Σ K R^ → Void)]
   [⊔ᵥ! : (Σ α (U V V^) → Void)]))

(define-signature kont^
  ([mk-=>i : (Σ H (Listof Dom) → ==>i)]
   ))

#;(define-signature app^
  ([app : (ℓ V^ (Listof V^) -H -φ -Σ K → (℘ -ς))]
   [app₁ : ([ℓ -V (Listof V^) -H -φ -Σ K] [#:switched? Boolean] . ->* . (℘ -ς))]
   [app/rest/unsafe : (ℓ -V (Listof V^) -V -H -φ -Σ K → (℘ -ς))]))

#;(define-signature mon^
  ([mon : (Ctx V^ V^ -H -φ -Σ K → (℘ -ς))]
   [push-mon : ((Ctx V^ V^ -H -φ -Σ K) (#:looped Boolean) . ->* . (℘ -ς))]))

#;(define-signature fc^
  ([flat-chk : (-l ℓ V^ V^ -H -φ -Σ K → (℘ -ς))]
   [push-fc : ((-l ℓ V^ V^ -H -φ -Σ K) (#:looped Boolean) . ->* . (℘ -ς))]))

#;(define-signature memoize^
  ([memoize⟦E⟧ : (⟦E⟧ → ⟦E⟧)]))

#;(define-signature havoc^
  ([havoc : (HV-Tag -φ -Σ K → (℘ -ς))]
   [gen-havoc-expr : ((Listof -module) → -e)]
   [add-leak! : (HV-Tag -Σ -φ (U V^ (Listof V^)) → -φ)]))
