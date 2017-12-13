#lang typed/racket/base

(provide compile^ kont^ app^ fc^ mon^ memoize^ havoc^)

(require typed/racket/unit
         set-extras
         "../utils/bijection.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(define-signature compile^
  ([↓ₚ : ((Listof -module) -e → -⟦e⟧)]
   [↓ₘ : (-module → -⟦e⟧)]
   [↓ₑ : (-l -e → -⟦e⟧)]
   [↓ₓ : (-l Symbol ℓ → -⟦e⟧)]
   [mk-V : (-V → -⟦e⟧)]
   [mk-A : (-A → -⟦e⟧)]
   [mk-app : (ℓ -⟦e⟧ (Listof -⟦e⟧) → -⟦e⟧)]
   [mk-mon : (-ctx -⟦e⟧ -⟦e⟧ → -⟦e⟧)]
   [mk-fc : (-l ℓ -⟦e⟧ -⟦e⟧ → -⟦e⟧)]
   [mk-wrapped-hash : (-Hash/C -ctx ⟪α⟫ -V^ → -⟦e⟧)]
   [mk-wrapped-set : (-Set/C -ctx ⟪α⟫ -V^ → -⟦e⟧)]))

(define-signature kont^
  ([rt : (-αₖ → -⟦k⟧)]
   [ap∷ : ((Listof -V^) (Listof -⟦e⟧) -ρ ℓ -⟦k⟧ → -⟦k⟧)]
   [set!∷ : (⟪α⟫ -⟦k⟧ → -⟦k⟧)]
   [let∷ : (ℓ
            (Listof Symbol)
            (Listof (Pairof (Listof Symbol) -⟦e⟧))
            (Listof (Pairof Symbol -V^))
            -⟦e⟧
            -ρ
            -⟦k⟧ →
            -⟦k⟧)]
   [letrec∷ : (ℓ
               (Listof Symbol)
               (Listof (Pairof (Listof Symbol) -⟦e⟧))
               -⟦e⟧
               -ρ
               -⟦k⟧ →
               -⟦k⟧)]
   [if∷ : (-l -⟦e⟧ -⟦e⟧ -ρ -⟦k⟧ → -⟦k⟧)]
   [bgn∷ : ((Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [bgn0.v∷ : ((Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [bgn0.e∷ : ((Listof -V^) (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [mon.c∷ : (-ctx (U (Pairof -⟦e⟧ -ρ) -V^) -⟦k⟧ → -⟦k⟧)]
   [mon.v∷ : (-ctx (U (Pairof -⟦e⟧ -ρ) -V^) -⟦k⟧ → -⟦k⟧)]
   [mon*.c∷ : (-ctx (U (Listof -⟪α⟫ℓ) 'any) -⟦k⟧ → -⟦k⟧)]
   [mon*∷ : (-ctx (Listof -V^) (Listof -V^) (Listof ℓ) (Listof -V^) -⟦k⟧ → -⟦k⟧)]
   [μ/c∷ : (Symbol -⟦k⟧ → -⟦k⟧)]
   [-->.dom∷ : ((Listof -V^) (Listof -⟦e⟧) (Option -⟦e⟧) -⟦e⟧ -ρ ℓ -⟦k⟧ → -⟦k⟧)]
   [-->.rst∷ : ((Listof -V^) -⟦e⟧ -ρ ℓ -⟦k⟧ → -⟦k⟧)]
   [-->.rng∷ : ((Listof -V^) (Option -V^) ℓ -⟦k⟧ → -⟦k⟧)]
   [-->i∷ : ((Listof -V^) (Listof -⟦e⟧) -ρ -Clo ℓ -⟦k⟧ → -⟦k⟧)]
   [struct/c∷ : (ℓ -𝒾 (Listof -V^) (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [def∷ : (-l (Listof ⟪α⟫) -⟦k⟧ → -⟦k⟧)]
   [dec∷ : (ℓ -𝒾 -⟦k⟧ → -⟦k⟧)]
   [hv∷ : (HV-Tag -⟦k⟧ → -⟦k⟧)]
   ;; Specific helpers
   [wrap-st∷ : (-St/C -ctx -⟦k⟧ → -⟦k⟧)]
   [mon-or/c∷ : (-ctx -V^ -V^ -V^ -⟦k⟧ → -⟦k⟧)]
   [mk-wrap-vect∷ : ((U -Vector/C -Vectorof) -ctx -⟦k⟧ → -⟦k⟧)]
   [if.flat/c∷ : (-V^ -blm -⟦k⟧ → -⟦k⟧)]
   [fc-and/c∷ : (-l ℓ -V^ -V^ -⟦k⟧ → -⟦k⟧)]
   [fc-or/c∷ : (-l ℓ -V^ -V^ -V^ -⟦k⟧ → -⟦k⟧)]
   [fc-not/c∷ : (-V^ -⟦k⟧ → -⟦k⟧)]
   [fc-struct/c∷ : (-l ℓ -𝒾 (Listof -V^) (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [fc.v∷ : (-l ℓ -⟦e⟧ -ρ -⟦k⟧ → -⟦k⟧)]
   [and∷ : (-l (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [or∷ : (-l (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [restore-ctx∷ : (-H -⟦k⟧ → -⟦k⟧)]
   [hash-set-inner∷ : (ℓ ⟪α⟫ -⟦k⟧ → -⟦k⟧)]
   [wrap-hash∷ : (-Hash/C -ctx -⟦k⟧ → -⟦k⟧)]
   [set-add-inner∷ : (ℓ ⟪α⟫ -⟦k⟧ → -⟦k⟧)]
   [wrap-set∷ : (-Set/C -ctx -⟦k⟧ → -⟦k⟧)]
   [maybe-havoc-prim-args∷ : (ℓ Symbol -⟦k⟧ → -⟦k⟧)]
   [make-prim-range∷ : (-ctx (Option (Listof -⟪α⟫ℓ)) (Listof -V^) (Listof (List (Listof -V) (Option -V) (Listof -V))) -⟦k⟧ → -⟦k⟧)]
   [implement-predicate∷ : (Symbol -⟦k⟧ → -⟦k⟧)]
   [absurd∷ : (-⟦k⟧ → -⟦k⟧)]
   [rename∷ : ((HashTable -t -t) -Γ -⟦k⟧ → -⟦k⟧)]
   [maybe-unshadow∷ : (-δσ -δσ -⟦k⟧ → -⟦k⟧)]
   [σₖ+! : (-Σ -αₖ -⟦k⟧ → -αₖ)]
   ;; Non-frame helpers
   [mk-=>i : (-Σ -H -φ (Listof -V^) -Clo ℓ → (Values -V -φ))]
   ))

(define-signature app^
  ([app : (ℓ -V^ (Listof -V^) -H -φ -Σ -⟦k⟧ → (℘ -ς))]
   [app₁ : ([ℓ -V (Listof -V^) -H -φ -Σ -⟦k⟧] [#:switched? Boolean] . ->* . (℘ -ς))]
   [app/rest/unsafe : (ℓ -V (Listof -V^) -V -H -φ -Σ -⟦k⟧ → (℘ -ς))]))

(define-signature mon^
  ([mon : (-ctx -V^ -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))]
   [push-mon : ((-ctx -V^ -V^ -H -φ -Σ -⟦k⟧) (#:looped Boolean) . ->* . (℘ -ς))]))

(define-signature fc^
  ([flat-chk : (-l ℓ -V^ -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))]
   [push-fc : ((-l ℓ -V^ -V^ -H -φ -Σ -⟦k⟧) (#:looped Boolean) . ->* . (℘ -ς))]))

(define-signature memoize^
  ([memoize-⟦e⟧ : (-⟦e⟧ → -⟦e⟧)]))

(define-signature havoc^
  ([havoc : (HV-Tag -φ -Σ -⟦k⟧ → (℘ -ς))]
   [gen-havoc-expr : ((Listof -module) → -e)]
   [add-leak! : (HV-Tag -Σ -φ (U -V^ (Listof -V^)) → -φ)]))
