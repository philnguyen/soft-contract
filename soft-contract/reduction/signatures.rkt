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
  [F:Ap (Listof V^) (Listof (U EΡ V^)) ℓ]
  [F:Set! α]
  [F:Let ℓ (Listof Symbol) (Assoc (Listof Symbol) ⟦E⟧) (Assoc Symbol V^) ⟦E⟧ Ρ]
  [F:Letrec ℓ (Listof Symbol) (Assoc (Listof Symbol) ⟦E⟧) ⟦E⟧ Ρ]
  [F:If -l ⟦E⟧ ⟦E⟧ Ρ]
  [F:Bgn (NeListof ⟦E⟧) Ρ]
  [F:Bgn0:V (NeListof ⟦E⟧) Ρ]
  [F:Bgn0:E W^ (Listof ⟦E⟧) Ρ]
  [F:Mon:C Ctx (U EΡ V^)]
  [F:Mon:V Ctx (U EΡ V^)]
  [F:Mon*:C Ctx (Option (Listof αℓ))]
  [F:Mon* Ctx W W (Listof ℓ) W]
  [F:Μ/C Symbol]
  [F:==>:Dom W (Listof ⟦E⟧) (Option ⟦E⟧) ⟦E⟧ Ρ ℓ]
  [F:==>:Rst W ⟦E⟧ Ρ ℓ]
  [F:==>:Rng W (Option V^) ℓ]
  [F:==>i Ρ (Listof Dom) (Pairof Symbol ℓ) (Listof ⟦dom⟧)]
  [F:St/C ℓ -𝒾 W (Listof ⟦E⟧) Ρ]
  [F:Def -l (Listof α)]
  [F:Dec ℓ -𝒾]
  ;; Specific helpers
  [F:Wrap Prox/C Ctx α]
  [F:Mon-Or/C Ctx V^ V^ V^]
  [F:If:Flat/C V^ Blm]
  [F:Fc-And/C -l ℓ V^ V^]
  [F:Fc-Or/C -l ℓ V^ V^ V^]
  [F:Fc-Not/C V^]
  [F:Fc-Struct/C -l ℓ -𝒾 W (Listof ⟦E⟧) Ρ]
  [F:Fc:V -l ℓ ⟦E⟧ Ρ] 
  [F:Hash-Set-Inner ℓ α]
  [F:Set-Add-Inner ℓ α]
  [F:Maybe-Havoc-Prim-Args ℓ Symbol]
  [F:Make-Prim-Range Ctx (Option (Listof αℓ)) W (Listof (List (Listof V) (Option V) (Listof V)))]
  [F:Implement-Predicate Symbol]
  [F:Absurd])

(define-substructs -α
  (-α:top -𝒾)
  (-α:wrp -𝒾)
  
  ; for binding
  (-α:x Symbol H)
  ; for struct field
  (-α:fld -𝒾 ℓ H Index)
  ; for Cons/varargs
  ; idx prevents infinite list
  (-α:var:car (U ℓ Symbol) H (Option Natural))
  (-α:var:cdr (U ℓ Symbol) H (Option Natural))

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
  (-α:hv (U (Pairof -l H) #f))
  (-α:mon-x/c Symbol H -l)
  (-α:fc-x/c Symbol H))

(define-signature alloc^
  ([mutable? : (α → Boolean)]
   [bind-args! : (Ρ -formals W H Σ → Ρ)]
   [bind-rest! : ([Ρ Symbol W H Σ] [#:end V] . ->* . Ρ)]
   [alloc-rest! : ([(U Symbol ℓ) W H Σ] [#:end V] . ->* . V)]
   [H+ : (H ℓ (U ⟦E⟧ V #f) (U 'app 'mon) → (Values H Boolean))] 
   [H₀ : H]))

(define-signature compile^
  ([↓ₚ : (-prog → ⟦E⟧)]
   [↓ₘ : (-module → ⟦E⟧)]
   [↓ₑ : (-l -e → ⟦E⟧)]
   [↓ₓ : (Symbol ℓ → ⟦E⟧)]
   [mk-V : ((U V V^) → ⟦E⟧)]
   [mk-W : (W → ⟦E⟧)]
   [mk-Blm : (Blm → ⟦E⟧)]
   [mk--> : (ℓ (-var ⟦E⟧) ⟦E⟧ → ⟦E⟧)]
   [mk-->i : ((Listof ⟦dom⟧) ⟦dom⟧ → ⟦E⟧)]
   [mk-app : (ℓ ⟦E⟧ (Listof ⟦E⟧) → ⟦E⟧)]
   [mk-mon : (Ctx ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-fc : (-l ℓ ⟦E⟧ ⟦E⟧ → ⟦E⟧)]
   [mk-let* : (ℓ (Listof (Pairof Symbol ⟦E⟧)) ⟦E⟧ → ⟦E⟧)]
   [mk-wrapped : (Prox/C Ctx α V^ → ⟦E⟧)]
   [split-⟦dom⟧s : (Ρ (Listof ⟦dom⟧) → (Values (Listof Dom) (Listof ⟦dom⟧)))]
   ))


(define-signature step^
  ([inj : ((U -prog ⟦E⟧) → (Values Ξ Σ))]
   [↝* : ((U -prog ⟦E⟧) → (Values (℘ Blm) Σ))]
   [↝  : (Ξ Σ → (℘ Ξ))]
   [ret! : [(U R R^) Ξ:co Σ → Ξ:co]]
   [K+/And : (-l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)]
   [K+/Or  : (-l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)]
   [with-guarded-arity/W : (W Natural ℓ (W → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-arity : (R^ Natural ℓ (R^ → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-arity/collapse : (R^ Natural ℓ (W Φ^ → (℘ Ξ)) → (℘ Ξ))]
   [with-guarded-single-arity/collapse : (R^ ℓ (V^ Φ^ → (℘ Ξ)) → (℘ Ξ))]
   [db:iter? : (Parameterof Boolean)]
   [db:max-steps : (Parameterof (Option Integer))]))

(define-signature app^
  ([app  : (V^ W ℓ Φ^ Ξ:co Σ → (℘ Ξ))]
   [app₁ : (V → ⟦F⟧^)]
   [app/rest/unsafe : (V W V ℓ Φ^ Ξ:co Σ → (℘ Ξ))]))

(define-signature mon^
  ([mon : (V^ V^ Ctx Φ^ Ξ:co Σ → (℘ Ξ))]))

(define-signature fc^
  ([fc : (V^ V^ ℓ Φ^ Ξ:co Σ → (℘ Ξ))]))

(define-signature havoc^
  ([havoc : (HV-Tag R^ Ξ:co Σ → (℘ Ξ))]
   [gen-havoc-expr : ((Listof -module) → -e)]
   [add-leak! : (HV-Tag Σ (U V^ W) → Void)]))

(define-signature for-gc^
  ([V-root : (V → (℘ α))]))
