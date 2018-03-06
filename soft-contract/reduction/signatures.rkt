#lang typed/racket/base

(provide #|compile^ kont^ app^ fc^ mon^ memoize^ havoc^|#)

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
  [K:Mon:c Ctx (U (Pairof ⟦E⟧ Ρ) V^) K]
  [K:Mon:V Ctx (U (Pairof ⟦E⟧ Ρ) V^) K]
  [K:Mon*:c Ctx (U (Listof αℓ) 'any) K]
  [K:Mon* Ctx (Listof V^) (Listof V^) (Listof ℓ) (Listof V^) K]
  [K:Μ/C Symbol K]
  [K:==>.Dom (Listof V^) (Listof ⟦E⟧) (Option ⟦E⟧) ⟦E⟧ Ρ ℓ K]
  [K:==>.Rst (Listof V^) ⟦E⟧ Ρ ℓ K]
  [K:==>.Rng (Listof V^) (Option V^) ℓ K]
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

#;(define-signature compile^
  ([↓ₚ : ((Listof -module) -e → ⟦E⟧)]
   [↓ₘ : (-module → ⟦E⟧)]
   [↓ₑ : (-l -e → ⟦E⟧)]
   [↓ₓ : (Symbol ℓ → ⟦E⟧)]
   [mk--> : (ℓ (-maybe-var ⟦E⟧) ⟦E⟧ → ⟦E⟧)]
   [mk-->i : ((Listof -⟦dom⟧) -⟦dom⟧ → ⟦E⟧)]
   [mk-V : (-V → ⟦E⟧)]
   [mk-A : (-A → ⟦E⟧)]
   [mk-app : (ℓ ⟦E⟧ (Listof ⟦E⟧) → ⟦E⟧)]
   [mk-mon : (Ctx ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-fc : (-l ℓ ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-wrapped-hash : (-Hash/C Ctx α V^ → ⟦E⟧)]
   [mk-wrapped-set : (Set/C Ctx α V^ → ⟦E⟧)]
   [mk-let* : (ℓ (Listof (Pairof Symbol ⟦E⟧)) ⟦E⟧ → ⟦E⟧)]
   [split-⟦dom⟧s : (Ρ (Listof -⟦dom⟧) → (Values (Listof Dom) (Listof -⟦dom⟧)))]))

#;(define-signature kont^
  ([rt : (-αₖ → K)]
   [ap : ((Listof V^) (Listof ⟦E⟧) Ρ ℓ K → K)]
   [set! : (α K → K)]
   [let : (ℓ
            (Listof Symbol)
            (Listof (Pairof (Listof Symbol) ⟦E⟧))
            (Listof (Pairof Symbol V^))
            ⟦E⟧
            Ρ
            K →
            K)]
   [letrec : (ℓ
               (Listof Symbol)
               (Listof (Pairof (Listof Symbol) ⟦E⟧))
               ⟦E⟧
               Ρ
               K →
               K)]
   [if : (-l ⟦E⟧ ⟦E⟧ Ρ K → K)]
   [bgn : ((Listof ⟦E⟧) Ρ K → K)]
   [bgn0.v : ((Listof ⟦E⟧) Ρ K → K)]
   [bgn0.e : ((Listof V^) (Listof ⟦E⟧) Ρ K → K)]
   [mon.c : (Ctx (U (Pairof ⟦E⟧ Ρ) V^) K → K)]
   [mon.v : (Ctx (U (Pairof ⟦E⟧ Ρ) V^) K → K)]
   [mon*.c : (Ctx (U (Listof -αℓ) 'any) K → K)]
   [mon* : (Ctx (Listof V^) (Listof V^) (Listof ℓ) (Listof V^) K → K)]
   [μ/c : (Symbol K → K)]
   [-->.dom : ((Listof V^) (Listof ⟦E⟧) (Option ⟦E⟧) ⟦E⟧ Ρ ℓ K → K)]
   [-->.rst : ((Listof V^) ⟦E⟧ Ρ ℓ K → K)]
   [-->.rng : ((Listof V^) (Option V^) ℓ K → K)]
   [-->i : (Ρ (Listof Dom) (Pairof Symbol ℓ) (Listof -⟦dom⟧) K → K)]
   [struct/c : (ℓ -𝒾 (Listof V^) (Listof ⟦E⟧) Ρ K → K)]
   [def : (-l (Listof α) K → K)]
   [dec : (ℓ -𝒾 K → K)]
   [hv : (HV-Tag K → K)]
   ;; Specific helpers
   [wrap-st : (St/C Ctx K → K)]
   [mon-or/c : (Ctx V^ V^ V^ K → K)]
   [mk-wrap-vect : ((U -Vect/C -Vectof) Ctx K → K)]
   [if.flat/c : (V^ -blm K → K)]
   [fc-and/c : (-l ℓ V^ V^ K → K)]
   [fc-or/c : (-l ℓ V^ V^ V^ K → K)]
   [fc-not/c : (V^ K → K)]
   [fc-struct/c : (-l ℓ -𝒾 (Listof V^) (Listof ⟦E⟧) Ρ K → K)]
   [fc.v : (-l ℓ ⟦E⟧ Ρ K → K)]
   [and : (-l (Listof ⟦E⟧) Ρ K → K)]
   [or : (-l (Listof ⟦E⟧) Ρ K → K)]
   [restoreCtx : (-H K → K)]
   [hash-set-inner : (ℓ α K → K)]
   [wrap-hash : (-Hash/C Ctx K → K)]
   [set-add-inner : (ℓ α K → K)]
   [wrap-set : (Set/C Ctx K → K)]
   [maybe-havoc-prim-args : (ℓ Symbol K → K)]
   [make-prim-range : (Ctx (Option (Listof -αℓ)) (Listof V^) (Listof (List (Listof -V) (Option -V) (Listof -V))) K → K)]
   [implement-predicate : (Symbol K → K)]
   [absurd : (K → K)]
   [rename : (Uni -Γ K → K)]
   [maybe-unshadow : (-δσ -δσ K → K)]
   [σₖ+! : (-Σ -αₖ K → -αₖ)]
   ;; Non-frame helpers
   [mk-=>i : (-Σ -H -φ (Listof Dom) → -=>i)]
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
