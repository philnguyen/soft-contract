#lang typed/racket/base

(provide compile^ kont^ app^ mon^ memoize^ havoc^)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/signatures.rkt")

(define-signature compile^
  ([↓ₚ : ((Listof -module) -e → -⟦e⟧)]
   [↓ₘ : (-module → -⟦e⟧)]
   [↓ₑ : (-l -e → -⟦e⟧)]
   [↓ₓ : (-l Symbol → -⟦e⟧)]
   [↓ₚᵣₘ : (-prim → -⟦e⟧)]
   [mk-app : (ℓ -⟦e⟧ (Listof -⟦e⟧) → -⟦e⟧)]
   [mk-mon : (-l³ ℓ -⟦e⟧ -⟦e⟧ → -⟦e⟧)]
   [mk-rt : ((U -A -W¹) → -⟦e⟧)]
   [mk-fc : (-l ℓ -⟦e⟧ -⟦e⟧ → -⟦e⟧)]))

(define-signature kont^
  ([rt : (-αₖ → -⟦k⟧)]
   [ap∷ : ((Listof -W¹) (Listof -⟦e⟧) -ρ ℓ -⟦k⟧ → -⟦k⟧)]
   [set!∷ : (⟪α⟫ -⟦k⟧ → -⟦k⟧)]
   [let∷ : (ℓ
            (Listof Symbol)
            (Listof (Pairof (Listof Symbol) -⟦e⟧))
            (Listof (Pairof Symbol -W¹))
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
   [bgn0.e∷ : (-W (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [mon.c∷ : (-l³ ℓ (U (Pairof -⟦e⟧ -ρ) -W¹) -⟦k⟧ → -⟦k⟧)]
   [mon.v∷ : (-l³ ℓ (U (Pairof -⟦e⟧ -ρ) -W¹) -⟦k⟧ → -⟦k⟧)]
   [mon*.c∷ : (-l³ ℓ (U (Listof -⟪α⟫ℓ) 'any) -?t -⟦k⟧ → -⟦k⟧)]
   [mon*∷ : (-l³ ℓ (Listof -W¹) (Listof -W¹) (Listof ℓ) (Listof -W¹) -⟦k⟧ → -⟦k⟧)]
   [μ/c∷ : (Symbol -⟦k⟧ → -⟦k⟧)]
   [-->.dom∷ : ((Listof -W¹) (Listof -⟦e⟧) (Option -⟦e⟧) -⟦e⟧ -ρ ℓ -⟦k⟧ → -⟦k⟧)]
   [-->.rst∷ : ((Listof -W¹) -⟦e⟧ -ρ ℓ -⟦k⟧ → -⟦k⟧)]
   [-->.rng∷ : ((Listof -W¹) (Option -W¹) ℓ -⟦k⟧ → -⟦k⟧)]
   [-->i∷ : ((Listof -W¹) (Listof -⟦e⟧) -ρ -Clo -λ ℓ -⟦k⟧ → -⟦k⟧)]
   [case->∷ : (ℓ (Listof (Listof -W¹)) (Listof -W¹) (Listof -⟦e⟧) (Listof (Listof -⟦e⟧)) -ρ -⟦k⟧ → -⟦k⟧)]
   [struct/c∷ : (ℓ -𝒾 (Listof -W¹) (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [def∷ : (-l (Listof ⟪α⟫) -⟦k⟧ → -⟦k⟧)]
   [dec∷ : (ℓ -𝒾 -⟦k⟧ → -⟦k⟧)]
   [hv∷ : (-⟦k⟧ → -⟦k⟧)]
   ;; Specific helpers
   [wrap-st∷ : (-𝒾 -?t -St/C ℓ -l³ -⟦k⟧ → -⟦k⟧)]
   [mon-or/c∷ : (-l³ ℓ -W¹ -W¹ -W¹ -⟦k⟧ → -⟦k⟧)]
   [mk-wrap-vect∷ : (-?t (U -Vector/C -Vectorof) ℓ -l³ -⟦k⟧ → -⟦k⟧)]
   [if.flat/c∷ : (-W -blm -⟦k⟧ → -⟦k⟧)]
   [fc-and/c∷ : (-l ℓ -W¹ -W¹ -⟦k⟧ → -⟦k⟧)]
   [fc-or/c∷ : (-l ℓ -W¹ -W¹ -W¹ -⟦k⟧ → -⟦k⟧)]
   [fc-not/c∷ : (-l -W¹ -W¹ -⟦k⟧ → -⟦k⟧)]
   [fc-struct/c∷ : (-l ℓ -𝒾 (Listof -W¹) (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [fc.v∷ : (-l ℓ -⟦e⟧ -ρ -⟦k⟧ → -⟦k⟧)]
   [and∷ : (-l (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [or∷ : (-l (Listof -⟦e⟧) -ρ -⟦k⟧ → -⟦k⟧)]
   [mk-listof∷ : (-?t ℓ -⟪ℋ⟫ -⟦k⟧ → -⟦k⟧)]
   ;; Non-frame helpers
   [mk-=>i! : (-Σ -Γ -⟪ℋ⟫ (Listof -W¹) -Clo -λ ℓ → (Values -V -?t))]
   ))

(define-signature app^
  ([app : (ℓ -W¹ (Listof -W¹) -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))]
   [app/rest/unsafe : (ℓ -W¹ (Listof -W¹) -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))]))

(define-signature mon^
  ([mon : (-l³ ℓ -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))]
   [push-mon : (-l³ ℓ -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → -ς↑)]
   [flat-chk : (-l ℓ -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))]
   [push-fc : (-l ℓ -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → -ς↑)]))

(define-signature memoize^
  ([memoize-⟦e⟧ : (-⟦e⟧ → -⟦e⟧)]
   [memoize-⟦k⟧ : (-⟦k⟧ → -⟦k⟧)]))

(define-signature havoc^
  ([havoc : (-$ -⟪ℋ⟫ -Σ → (℘ -ς))]
   [gen-havoc-expr : ((Listof -module) → -e)]))
