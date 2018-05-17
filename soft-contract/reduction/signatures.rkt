#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         bnf
         set-extras
         "../utils/list.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(EΡ . ::= . (EΡ [code : ⟦E⟧] [env : Ρ]))

(define-substructs F
  [F:Ap (Listof T^) (Listof (U EΡ T^)) ℓ]
  [F:Set! α]
  [F:Let ℓ (Listof Symbol) (Assoc (Listof Symbol) ⟦E⟧) (Assoc Symbol T^) ⟦E⟧ Ρ]
  [F:Letrec ℓ (Listof Symbol) (Assoc (Listof Symbol) ⟦E⟧) ⟦E⟧ Ρ]
  [F:If -l ⟦E⟧ ⟦E⟧ Ρ]
  [F:Bgn (NeListof ⟦E⟧) Ρ]
  [F:Bgn0:V (NeListof ⟦E⟧) Ρ]
  [F:Bgn0:E W^ (Listof ⟦E⟧) Ρ]
  [F:Mon:C Ctx (U EΡ T^)]
  [F:Mon:V Ctx (U EΡ T^)]
  [F:Mon*:C Ctx (Option (Listof αℓ))]
  [F:Mon* Ctx W W (Listof ℓ) W]
  [F:Μ/C Symbol]
  [F:==>:Dom W (Listof ⟦E⟧) (Option ⟦E⟧) ⟦E⟧ Ρ ℓ]
  [F:==>:Rst W ⟦E⟧ Ρ ℓ]
  [F:==>:Rng W (Option T^) ℓ]
  [F:==>i Ρ (Listof Dom) (Pairof Symbol ℓ) (Listof ⟦dom⟧)]
  [F:St/C ℓ -𝒾 W (Listof ⟦E⟧) Ρ]
  [F:Def -l (Listof α)]
  [F:Dec ℓ -𝒾]
  ;; Specific helpers
  [F:Wrap Prox/C Ctx α]
  [F:Mon-Or/C Ctx V^ V^ T^]
  [F:If:Flat/C T^ (℘ Blm)]
  [F:Fc-And/C α αℓ]
  [F:Fc-Or/C α αℓ T^]
  [F:Fc-Not/C T^]
  [F:Fc-Struct/C ℓ -𝒾 W (Listof EΡ)]
  [F:Fc:V ℓ ⟦E⟧ Ρ]
  [F:Fc:C ℓ T^]
  [F:Hash-Set-Inner ℓ α]
  [F:Set-Add-Inner ℓ α]
  [F:Havoc-Prim-Args ℓ Symbol]
  [F:Make-Prim-Range Ctx (Option (Listof αℓ)) W (Listof (List (Listof V) (Option V) (Listof V)))]
  [F:Implement-Predicate Symbol]
  [F:Havoc]
  [F:Absurd]) 

(define-signature alloc^
  ([mutable? : (α → Boolean)]
   [bind-args! : (Φ^ Ρ -formals W H Σ → (Values Φ^ Ρ))]
   [alloc-rest! : ([(U Symbol ℓ) W H Φ^ Σ] [#:end T^] . ->* . T^)]
   [H+ : (H ℓ (U Clo ℓ Symbol #f) → H)]
   [looped? : (H → Boolean)]
   [scope : (H → (℘ α))] ; TODO not used
   [H₀ : H]))

(define-signature compile^
  ([↓ₚ : (-prog → ⟦E⟧)]
   [↓ₘ : (-module → ⟦E⟧)]
   [↓ₑ : (-l -e → ⟦E⟧)]
   [↓ₓ : (Symbol ℓ → ⟦E⟧)]
   [mk-T : ((U T T^) → ⟦E⟧)]
   [mk-W : (W → ⟦E⟧)]
   [mk-Blm : (Blm → ⟦E⟧)]
   [mk--> : (ℓ (-var ⟦E⟧) ⟦E⟧ → ⟦E⟧)]
   [mk-->i : ((Listof ⟦dom⟧) ⟦dom⟧ → ⟦E⟧)]
   [mk-app : (ℓ ⟦E⟧ (Listof ⟦E⟧) → ⟦E⟧)]
   [mk-mon : (Ctx ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-fc : (ℓ ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-let* : (ℓ (Listof (Pairof Symbol ⟦E⟧)) ⟦E⟧ → ⟦E⟧)]
   [mk-wrapped : (Prox/C Ctx α T^ → ⟦E⟧)]
   [split-⟦dom⟧s : (Ρ (Listof ⟦dom⟧) → (Values (Listof Dom) (Listof ⟦dom⟧)))]
   ))


(define-signature step^
  ([inj : ((U -prog ⟦E⟧) → (Values Ξ Σ))]
   [↝* : ((U -prog ⟦E⟧) → (Values (℘ Blm) Σ))]
   [↝  : (Ξ Σ → (℘ Ξ))]
   [ret! : ((U R R^) Ξ:co Σ → Ξ:co)]
   [blm : (ℓ -l (Listof (U V V^)) (U W W^) → (℘ Blm))]
   [K+/And : (-l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)]
   [K+/Or  : (-l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)]
   [with-arity : (Σ R^ (Index R → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-arity/W : (W Natural ℓ (W → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-arity : (R^ Natural ℓ (R^ → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-arity/collapse : (Σ R^ Natural ℓ (W Φ^ → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-single-arity/collapse : (Σ R^ ℓ (T^ Φ^ → (℘ Ξ)) → (℘ Ξ))]
   [with-check : (Σ Φ^ Ctx T^ P (R^ → (℘ Ξ)) → (℘ Ξ))]
   [R↓ : (Σ (℘ α) → R → R)]
   [db:iter? : (Parameterof Boolean)]
   [db:max-steps : (Parameterof (Option Integer))]))

(define-signature app^
  ([app  : (T^ W ℓ Φ^ Ξ:co Σ → (℘ Ξ))]
   [app₁ : (V → ⟦F⟧^)]
   [app-opq : ⟦F⟧^]
   [app/rest/unsafe : (T W T ℓ Φ^ Ξ:co Σ → (℘ Ξ))]))

(define-signature mon^
  ([mon : (T^ T^ Ctx Φ^ Ξ:co Σ → (℘ Ξ))]))

(define-signature fc^
  ([fc : (T^ T^ ℓ Φ^ Ξ:co Σ → (℘ Ξ))]))

(define-signature havoc^
  ([havoc : (HV-Tag R^ Ξ:co Σ → (℘ Ξ))]
   [gen-havoc-expr : ((Listof -module) → -e)]
   [add-leak! : (HV-Tag Σ V^ → Void)]))

(define-signature termination^
  ([update-call-record : (M Clo W ℓ Φ^ Σ → (Option M))]))

(define-signature approx^
  ([collapse-R^-1 : ((U Σ Σᵥ) R^ → (Values T^ Φ^))]
   [collapse-value-lists : ((U Σ Σᵥ) R^ Natural → R)]
   [R⊕ : ((U Σ Σᵥ) R R → R)]
   [⊔ₐ! : (Σ Ξ:co (U R R^) → Void)]
   [⊔ᵥ! : (Σ α (U V V^) → Void)]
   [⊔ᵥ*! : (Σ (Listof α) (Listof V^) → Void)]
   [⊔ₖ! : (Σ αₖ Ξ:co → Void)]
   [⊔T! : (Σ Φ^ α (U T T^) → Void)]
   [⊔T*! : (Σ Φ^ (Listof α) (Listof T^) → Void)]))

(define-signature for-gc^
  ([V-root : (V → (℘ α))]))
