#lang typed/racket/base

(provide app@)

(require (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/match
         (only-in racket/list split-at)
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit app@
  (import static-info^ ast-pretty-print^
          env^ sto^ val^ evl^
          prims^
          prover^
          compile^ step^ alloc^ havoc^)
  (export app^)
  (init-depend step^)

  (: app : V^ W ℓ Φ^ Ξ:co Σ → (℘ Ξ))
  (define (app Vₕ^ Wₓ ℓ Φ^ Ξ₀ Σ)
    (define with (inst with-2-paths Ξ))
    (with (λ () (split-results Σ (R (list Vₕ^) Φ^) 'procedure? #:fast? #t))
      (λ (R^)
        (define n {set (-b (length Wₓ))})
        (for/union : (℘ Ξ) ([Rᵢ (in-set R^)])
          (match-define (R (list Vₕ) Φ^) Rᵢ)
          (define a (map/set ((inst compose V (Option Arity) -b) -b V-arity) Vₕ))
          (with (λ () (split-results Σ (R (list a n) Φ^) 'arity-includes? #:fast? #t))
            (λ (Rs)
              (for/union : (℘ Ξ) ([Rᵢ (in-set Rs)]
                                  [Φ^ (in-value (R-_1 Rᵢ))]
                                  [Vₕ (in-set (car (R-_0 Rᵢ)))])
                ((app₁ Vₕ) Wₓ ℓ Φ^ Ξ₀ Σ)))
            (λ (Rs)
              (define msg (string->symbol (format "(arity-includes/c ~a)" (length Wₓ))))
              (blm ℓ 'Λ (list msg) (list Vₕ))))))
      (λ (R^)
        (blm ℓ 'Λ '(procedure?) (list Vₕ^)))))

  (: app₁ : V → ⟦F⟧^)
  ;; Apply single function, assuming function-ness and arity has been checked
  (define app₁
    (match-lambda
      [(Clo xs ⟦E⟧ Ρ) (app-clo xs ⟦E⟧ Ρ)]
      [(Case-Clo cases) (app-case-clo cases)]
      [(-st-mk 𝒾) (app-st-mk 𝒾)]
      [(-st-p 𝒾) (app-st-p 𝒾)]
      [(-st-ac 𝒾 i) (app-st-ac 𝒾 i)]
      [(-st-mut 𝒾 i) (app-st-mut 𝒾 i)]
      [(? symbol? o) (get-prim o)]
      [(X/G ctx (? Fn/C? G) α)
       (cond [(==>? G) (app-==> ctx G α)]
             [(==>i? G) (app-==>i ctx G α)]
             [(∀/C? G) (app-∀/C ctx G α)]
             [else (app-Case-=> ctx G α)])]
      [(And/C #t (αℓ α₁ _) (αℓ α₂ _)) (app-And/C α₁ α₂)]
      [(Or/C  #t (αℓ α₁ _) (αℓ α₂ _)) (app-Or/C α₁ α₂)]
      [(Not/C (αℓ α _)) (app-Not/C α)]
      [(St/C #t 𝒾 αℓs) (app-St/C 𝒾 (map αℓ-_0 αℓs))]
      [(-● Ps) app-opq]
      [(? S? S) (app-sym S)]))

  (: app/rest/unsafe : V W V ℓ Φ^ Ξ:co Σ → (℘ Ξ))
  (define (app/rest/unsafe Vₕ Wₓ Vᵣ ℓ Φ^ Ξ Σ)
    ???)

  (: app-clo : -formals ⟦E⟧ Ρ → ⟦F⟧^)
  (define ((app-clo fmls ⟦E⟧ Ρ) Wₓ ℓ Φ^ Ξ Σ)
    (match-define (Ξ:co _ M H) Ξ)
    (define-values (H* looped?) (H+ H ℓ ⟦E⟧ 'app))
    ;; FIXME guard arity
    (define Ρ* (bind-args! Ρ fmls Wₓ H* Σ))
    (define α* (αₖ ⟦E⟧ Ρ*))
    (⊔ₖ! Σ α* Ξ)
    {set (⟦E⟧ Ρ* Φ^ (Ξ:co (K '() α*) M H*) Σ)})

  (: app-case-clo : (Listof Clo) → ⟦F⟧^)
  (define ((app-case-clo clos) Wₓ ℓ Φ^ Ξ Σ)
    (define n (length Wₓ))
    (match-define (Clo x ⟦E⟧ Ρ) ; assume arity already checked
      ((inst findf Clo) (λ (clo) (arity-includes? (V-arity clo) n)) clos))
    ((app-clo x ⟦E⟧ Ρ) Wₓ ℓ Φ^ Ξ Σ))

  (: app-st-mk : -𝒾 → ⟦F⟧^)
  (define ((app-st-mk 𝒾) Wₓ ℓ Φ^ Ξ Σ)
    (define n (count-struct-fields 𝒾))
    (define H (Ξ:co-ctx Ξ))
    (define αs (build-list n (λ ([i : Index]) (mk-α (-α:fld 𝒾 ℓ H i)))))
    (⊔ᵥ*! Σ αs Wₓ)
    {set (ret! (V->R (St 𝒾 αs) Φ^) Ξ Σ)})

  (: app-st-p : -𝒾 → ⟦F⟧^)
  (define ((app-st-p 𝒾) Wₓ ℓ Φ^ Ξ Σ)
    {set (ret! (implement-predicate Σ Φ^ (-st-p 𝒾) Wₓ) Ξ Σ)})

  (: app-st-ac : -𝒾 Index → ⟦F⟧^)
  (define ((app-st-ac 𝒾 i) Wₓ ℓ Φ^ Ξ₀ Σ)
    (define P (-st-p 𝒾))
    (define Ac (-st-ac 𝒾 i))
    (with-2-paths (λ () (split-results Σ (R Wₓ Φ^) P))
      (λ ([R^ : R^])
        (for*/set : (℘ Ξ) ([Rᵢ (in-set R^)]
                           [Φ^ᵢ (in-value (R-_1 Rᵢ))]
                           [V^ᵢ (in-list (R-_0 Rᵢ))]
                           [Vᵢ (in-set V^ᵢ)])
          (match Vᵢ
            [(St 𝒾* αs) (ret! (V->R (Σᵥ@ Σ (list-ref αs i)) Φ^ᵢ) Ξ₀ Σ)]
            [(X/G ctx (St/C _ 𝒾* αℓs) α)
             (define V^* (Σᵥ@ Σ α))
             (define Ξ* ; mutable field should be wrapped
               (if (struct-mutable? 𝒾 i)
                   (match-let ([(αℓ αᵢ ℓᵢ) (list-ref αℓs i)])
                     (K+ (F:Mon:C (Ctx-with-ℓ ctx ℓᵢ) (Σᵥ@ Σ αᵢ)) Ξ₀))
                   Ξ₀))
             (define F:Ac (F:Ap (list {set Ac}) '() (ℓ-with-id ℓ 'unwrap)))
             (ret! (V->R V^* Φ^ᵢ) (K+ F:Ac Ξ*) Σ)]
            [(? S? S) (ret! (V->R (S:@ Ac (list S)) Φ^ᵢ) Ξ₀ Σ)]
            [_ (ret! (V->R (-● ∅) Φ^ᵢ) Ξ₀ Σ)])))
      (λ ([R^ : R^])
        (blm ℓ (-𝒾-name 𝒾) (list P) (collapse-R^/W^ R^)))))

  (: app-st-mut : -𝒾 Index → ⟦F⟧^)
  (define ((app-st-mut 𝒾 i) Wₓ ℓ Φ^ Ξ₀ Σ)
    (match-define (list Vₛ Vᵥ) Wₓ)
    (define P (-st-p 𝒾))
    (define Mut (-st-mut 𝒾 i))
    (with-2-paths (λ () (split-results Σ (R (list Vₛ) Φ^) P))
      (λ ([R^ : R^])
        (for*/set : (℘ Ξ) ([Rᵢ (in-set R^)]
                           [Φ^ᵢ (in-value (R-_1 Rᵢ))]
                           [V^ᵢ (in-list (R-_0 Rᵢ))]
                           [Vᵢ (in-set V^ᵢ)])
          (match Vᵢ
            [(St 𝒾* αs)
             (⊔ᵥ! Σ (list-ref αs i) Vᵥ)
             (ret! (V->R -void Φ^ᵢ) Ξ₀ Σ)]
            [(X/G ctx (St/C _ 𝒾* αℓs) α)
             (match-define (αℓ αᵢ ℓᵢ) (list-ref αℓs i))
             (define Vₛ* (Σᵥ@ Σ α))
             (define Ξ*
               (let ([F:Set (F:Ap (list Vₛ* {set Mut}) '() (ℓ-with-id ℓ 'unwrap))]
                     [F:Mon (F:Mon:C (Ctx-with-ℓ (Ctx-flip ctx) ℓᵢ) (Σᵥ@ Σ αᵢ))])
                 (K+ F:Mon (K+ F:Set Ξ₀))))
             (ret! (V->R Vᵥ Φ^ᵢ) Ξ* Σ)]
            [_
             (add-leak! (cons #f (Ξ:co-ctx Ξ₀)) Σ Vᵥ)
             (ret! (V->R -void Φ^ᵢ) Ξ₀ Σ)])))
      (λ ([R^ : R^])
        (blm ℓ (-𝒾-name 𝒾) (list P) (collapse-R^/W^ R^)))))

  (:* app-And/C app-Or/C : α α → ⟦F⟧^)
  (define-values (app-And/C app-Or/C)
    (let ()
      (: app-Comb/C : (-l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co) → α α → ⟦F⟧^)
      (define (((app-Comb/C K+) α₁ α₂) Wₓ ℓ Φ^ Ξ Σ)
        (match-define (list Vₓ) Wₓ)
        (define V₁ (Σᵥ@ Σ α₁))
        (define V₂ (Σᵥ@ Σ α₂))
        (define ⟦rhs⟧ (mk-app ℓ (mk-V V₂) (list (mk-V Vₓ))))
        (app V₁ Wₓ ℓ Φ^ (K+ (ℓ-src ℓ) (list ⟦rhs⟧) ⊥Ρ Ξ) Σ))
      (values (app-Comb/C K+/And) (app-Comb/C K+/Or))))

  (: app-Not/C : α → ⟦F⟧^)
  (define ((app-Not/C α) Wₓ ℓ Φ^ Ξ Σ)
    (app (Σᵥ@ Σ α) Wₓ ℓ Φ^ (K+ (F:Ap (list {set 'not}) '() ℓ) Ξ) Σ))

  (: app-St/C : -𝒾 (Listof α) → ⟦F⟧^)
  (define ((app-St/C 𝒾 αs) Wₓ ℓ Φ^ Ξ Σ)
    ;; TODO fix ℓᵢ for each contract component
    (match Wₓ
      [(list (or (St 𝒾* _) (X/G _ (St/C _ 𝒾* _) _)))
       #:when (𝒾* . substruct? . 𝒾)
       (define ⟦chk-field⟧s : (Listof ⟦E⟧)
         (for/list ([α (in-list αs)] [i (in-naturals)] #:when (index? i))
           (define Cᵢ (Σᵥ@ Σ α))
           (define ac (-st-ac 𝒾 i))
           (mk-app ℓ (mk-V Cᵢ) (list (mk-app ℓ (mk-V ac) (list (mk-W Wₓ)))))))
       (app₁ (-st-p 𝒾) Wₓ ℓ Φ^ (K+/And (ℓ-src ℓ) ⟦chk-field⟧s ⊥Ρ Ξ) Σ)]
      [_ {set (ret! (V->R -ff Φ^) Ξ Σ)}]))

  (: app-==> : Ctx ==> α → ⟦F⟧^)
  (define ((app-==> ctx G α) Wₓ ℓ Φ^ Ξ Σ)
    (define ctx* (Ctx-flip ctx))
    (match-define (==> (-var Doms₀ Domᵣ) Rng ⇓?) G)
    (define Ξ* (K+ (F:Mon*:C (Ctx-with-ℓ ctx ℓ) Rng) Ξ))
    (define ℓ* (ℓ-with-src ℓ (Ctx-src ctx)))
    (define Vₕ^ (Σᵥ@ Σ α))
    (define-values (αs₀ ℓs₀) (unzip-by αℓ-_0 αℓ-_1 Doms₀))
    (define-values (W₀ Wᵣ) (split-at Wₓ (length αs₀)))
    (define ⟦X⟧s : (Listof EΡ)
      (for/list ([C^ (in-list (Σᵥ@* Σ αs₀))]
                 [Vₓ^ (in-list W₀)]
                 [ℓₓ (in-list ℓs₀)])
        (EΡ (mk-mon (Ctx-with-ℓ ctx* ℓₓ) (mk-V C^) (mk-V Vₓ^)) ⊥Ρ)))
    (match* (Doms₀ Domᵣ)
      [('() #f) (app Vₕ^ '() ℓ* Φ^ Ξ* Σ)]
      [((? pair?) #f)
       (match-let ([(cons (EΡ ⟦X⟧ _) ⟦X⟧s) ⟦X⟧s])
         {set (⟦X⟧ ⊥Ρ Φ^ (K+ (F:Ap (list Vₕ^) ⟦X⟧s ℓ*) Ξ*) Σ)})]
      [(_ (αℓ αᵣ ℓᵣ))
       (define Vᵣ (alloc-rest! ℓ Wᵣ (Ξ:co-ctx Ξ) Σ))
       (define ⟦X⟧ᵣ (mk-mon (Ctx-with-ℓ ctx* ℓᵣ) (mk-V (Σᵥ@ Σ αᵣ)) (mk-V Vᵣ)))
       (define Fn (list Vₕ^ {set 'apply}))
       (match ⟦X⟧s
         [(cons (cons ⟦X⟧ _) ⟦X⟧s)
          {set (⟦X⟧ ⊥Ρ Φ^ (K+ (F:Ap Fn `(,@⟦X⟧s ,⟦X⟧ᵣ) ℓ*) Ξ* Σ))}]
         [_
          {set (⟦X⟧ᵣ ⊥Ρ Φ^ (K+ (F:Ap Fn '() ℓ*) Ξ*) Σ)}])]))

  (: app-==>i : Ctx ==>i α → ⟦F⟧^)
  (define ((app-==>i ctx G αₕ) Wₓ ℓ Φ^ Ξ Σ)
    (define ctx* (Ctx-flip ctx))
    (match-define (==>i Doms Rng ⇓?) G)
    (define x->⟦x⟧
      (for/hasheq : (Immutable-HashTable Symbol ⟦E⟧) ([D (in-list Doms)])
        (match-define (Dom x _ ℓₓ) D)
        (values x (↓ₓ x ℓₓ))))
    (define C->⟦E⟧ : ((U Clo α) → ⟦E⟧)
      (match-lambda
        [(and Cₓ (Clo (-var zs _) _ _))
         (define ⟦z⟧s : (Listof ⟦E⟧) (for/list ([z (in-list zs)]) (hash-ref x->⟦x⟧ z)))
         (mk-app ℓ (mk-V Cₓ) ⟦z⟧s)]
        [(? integer? α) (mk-V (Σᵥ@ Σ αₕ))]))
    (define-values (xs ⟦x⟧s ⟦mon-x⟧s)
      (for/lists ([xs : (Listof Symbol)] [⟦x⟧s : (Listof ⟦E⟧)] [⟦mon⟧s : (Listof ⟦E⟧)])
                 ([D (in-list Doms)] [Vₓ (in-list Wₓ)])
        (match-define (Dom x Cₓ ℓₓ) D)
        (values x
                (hash-ref x->⟦x⟧ x)
                (mk-mon (Ctx-with-ℓ ctx* ℓₓ) (C->⟦E⟧ Cₓ) (mk-V Vₓ)))))
    (define ⟦inner-app⟧
      (let ([ℓ* (ℓ-with-src ℓ (Ctx-src ctx))])
        (mk-app ℓ* (mk-V (Σᵥ@ Σ αₕ)) ⟦x⟧s)))
    (define ⟦mon-app⟧
      (match-let ([(Dom _ D ℓᵣ) Rng])
        (mk-mon (Ctx-with-ℓ ctx ℓᵣ) (C->⟦E⟧ D) ⟦inner-app⟧)))
    (define ⟦comp⟧ (mk-let* ℓ (map (inst cons Symbol ⟦E⟧) xs ⟦mon-x⟧s) ⟦mon-app⟧))
    {set (⟦comp⟧ ⊥Ρ Φ^ Ξ Σ)})

  (: app-∀/C : Ctx ∀/C α → ⟦F⟧^)
  (define ((app-∀/C ctx G α) Wₓ ℓ Φ^ Ξ Σ)
    (define l-seal (Ctx-neg ctx))
    (match-define (∀/C xs ⟦C⟧ Ρ₀) G)
    (define H (Ξ:co-ctx Ξ))
    (define Ρ*
      (for/fold ([Ρ : Ρ Ρ₀]) ([x (in-list xs)])
        (define αₛ (mk-α (-α:imm (Seal/C x H l-seal))))
        (define αᵥ (mk-α (-α:sealed x H)))
        (Ρ+ Ρ x αₛ)))
    (define Ξ* (let ([F:Mon (F:Mon:V ctx (Σᵥ@ Σ α))]
                     [F:Ap (F:Ap '() Wₓ ℓ)])
                 (K+ F:Mon (K+ F:Ap Ξ))))
    {set (⟦C⟧ Ρ* Φ^ Ξ* Σ)})

  (: app-Case-=> : Ctx Case-=> α → ⟦F⟧^)
  (define ((app-Case-=> ctx G α) Wₓ ℓ Φ^ Ξ Σ)
    (define n (length Wₓ))
    (match-define (? values C) ; assume arity already checked
      ((inst findf ==>) (λ (C) (arity-includes? (guard-arity C) n))
                        (Case-=>-_0 G)))
    ((app-==> ctx C α) Wₓ ℓ Φ^ Ξ Σ))

  (: app-opq : ⟦F⟧^)
  (define (app-opq Wₓ ℓ Φ^ Ξ Σ)
    (define-values (H* _) (H+ (Ξ:co-ctx Ξ) ℓ #f 'app))
    (define tag (cons #f H*))
    (define α (αₖ tag ⊥Ρ))
    (add-leak! tag Σ Wₓ)
    (⊔ₖ! Σ α Ξ)
    {set (Ξ:co (K '() α) (Ξ:co-mark Ξ) H*)})

  (: app-sym : S → ⟦F⟧^)
  (define (app-sym S) app-opq) ; TOOD


  #| 
  (: apply-app-Ar : (-=> -V^ -ctx → ℓ (Listof -V^) -V -H -φ -Σ -⟦k⟧ → (℘ -ς)))
  (define ((apply-app-Ar C Vᵤ^ ctx) ℓ₀ Vᵢs Vᵣ H φ Σ ⟦k⟧)
    (match-define (-=> (-var αℓs₀ (-⟪α⟫ℓ αᵣ ℓᵣ)) Rng) C)
    ;; FIXME copied n pasted from app-Ar
    (define-values (αs₀ ℓs₀) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs₀))
    (define ctx* (ctx-neg ctx))
    (define Cᵢs (σ@/list Σ (-φ-cache φ) αs₀))
    (define Cᵣ (σ@ Σ (-φ-cache φ) αᵣ))
    (define ⟦mon-x⟧s : (Listof -⟦e⟧)
      (for/list ([Cₓ Cᵢs] [Vₓ Vᵢs] [ℓₓ : ℓ ℓs₀])
        (mk-mon (ctx-with-ℓ ctx* ℓₓ) (mk-A (list Cₓ)) (mk-A (list Vₓ)))))
    (define ⟦mon-x⟧ᵣ : -⟦e⟧
      (mk-mon (ctx-with-ℓ ctx* ℓᵣ) (mk-A (list Cᵣ)) (mk-V Vᵣ)))
    (define fn (list Vᵤ^ {set 'apply}))
    (define ⟦k⟧* (mon*.c∷ (ctx-with-ℓ ctx ℓ₀) Rng ⟦k⟧))
    (match ⟦mon-x⟧s
      ['()
       (⟦mon-x⟧ᵣ ⊥ρ H φ Σ (ap∷ fn '() ⊥ρ ℓ₀ ⟦k⟧*))]
      [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
       (⟦mon-x⟧₀ ⊥ρ H φ Σ (ap∷ fn `(,@ ⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ ℓ₀ ⟦k⟧*))]))

  (: app-opq : -V → -⟦f⟧)
  (define (app-opq Vₕ)
    (λ (ℓ Vs H φ Σ ⟦k⟧)
      (define tag
        (match Vₕ
          [(-Fn● _ t) t]
          [_ '†]))
      (define φ*
        (for/fold ([φ : -φ φ]) ([V (in-list Vs)])
          (add-leak! tag Σ φ V)))
      (define αₖ (-αₖ H (-HV tag) φ*))
      (define ⟦k⟧* (bgn0.e∷ (list {set (fresh-sym!)}) '() ⊥ρ ⟦k⟧))
      {set (-ς↑ (σₖ+! Σ αₖ ⟦k⟧*))}))

  (: app/rest/unsafe : ℓ -V (Listof -V^) -V -H -φ -Σ -⟦k⟧ → (℘ -ς))
  ;; Apply function with (in general, part of) rest arguments already allocated,
  ;; assuming that init/rest args are already checked to be compatible.
  (define (app/rest/unsafe ℓ V-func V-inits V-rest H φ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (define num-inits (length V-inits))
    (define arg-counts
      (for/set: : (℘ Arity) ([a (estimate-list-lengths σ (-φ-cache φ) V-rest)] #:when a)
        (match a
          [(? exact-nonnegative-integer? n) (+ num-inits n)]
          [(arity-at-least n) (arity-at-least (+ num-inits n))])))
    
    (: app-prim/rest : -o → (℘ -ς))
    (define (app-prim/rest o)
      (define V-rests (unalloc σ (-φ-cache φ) V-rest))
      (for/union : (℘ -ς) ([Vᵣs (in-set V-rests)])
        (app₁ ℓ o (append V-inits Vᵣs) H φ Σ ⟦k⟧)))

    (: app-clo/rest : -formals -⟦e⟧ -ρ → (℘ -ς))
    (define (app-clo/rest xs ⟦e⟧ ρ)
      (match xs
        ;; TODO: if we assume clo as rest-arg, this path may never be reached...
        [(? list? xs)
         (define n (length xs))
         (define num-remaining-inits (- n num-inits))
         (define Vᵣ-lists
           (for/set: : (℘ (Listof -V^)) ([Vᵣ-list (in-set (unalloc σ (-φ-cache φ) V-rest))]
                                         #:when (= num-remaining-inits (length Vᵣ-list)))
             Vᵣ-list))
         (for/union : (℘ -ς) ([Vᵣs Vᵣ-lists])
           ((app-clo xs ⟦e⟧ ρ) ℓ (append V-inits Vᵣs) H φ Σ ⟦k⟧))]
        [(-var zs z)
         (define n (length zs))
         (define num-remaining-inits (- n num-inits))

         (: app/adjusted-args : -φ (Listof -V^) -V → (℘ -ς))
         (define (app/adjusted-args φ V-inits V-rest)
           (define-values (ρ₁ φ₁) (bind-args Σ ρ ℓ H φ zs V-inits))
           (define αᵣ (-α->⟪α⟫ (-α.x z H)))
           (define ρ₂ (ρ+ ρ₁ z αᵣ))
           (define φ₂ (alloc Σ φ₁ αᵣ {set V-rest}))
           (⟦e⟧ ρ₂ H φ₂ Σ ⟦k⟧))
         
         (cond
           ;; Need to retrieve some more arguments from `V-rest` as part of inits
           [(<= 0 num-remaining-inits)
            (define pairs (unalloc-prefix σ (-φ-cache φ) V-rest num-remaining-inits))
            (for/union : (℘ -ς) ([pair (in-set pairs)])
              (match-define (cons V-init-more Vᵣ) pair)
              (define V-inits* (append V-inits V-init-more))
              (app/adjusted-args φ V-inits* Vᵣ))]
           ;; Need to allocate some init arguments as part of rest-args
           [else
            (define-values (V-inits* V-inits.rest) (split-at V-inits n))
            (define-values (V-rest* φ*) (alloc-rest-args Σ ℓ H φ V-inits.rest #:end V-rest))
            (app/adjusted-args φ* V-inits* V-rest*)])]))

    (: app-Ar/rest : -=>_ ⟪α⟫ -ctx → (℘ -ς))
    (define (app-Ar/rest C α ctx)
      (define Vᵤ^ (σ@ σ (-φ-cache φ) α))
      (match C
        [(-=> (-var αℓs₀ (-⟪α⟫ℓ αᵣ ℓᵣ)) _)
         (define n (length αℓs₀))
         (define num-remaining-inits (- n num-inits))
         (cond
           ;; Need to retrieve some more arguments from `V-rest` as part of inits
           [(<= 0 num-remaining-inits)
            (define pairs (unalloc-prefix σ (-φ-cache φ) V-rest num-remaining-inits))
            (for/union : (℘ -ς) ([unalloced (in-set pairs)])
              (match-define (cons V-init-more Vᵣ*) unalloced)
              (define V-inits* (append V-inits V-init-more))
              ((apply-app-Ar C Vᵤ^ ctx) ℓ V-inits* Vᵣ* H φ Σ ⟦k⟧))]
           ;; Need to allocate some init arguments as part of rest-args
           [else
            (define-values (V-inits* V-inits.rest) (split-at V-inits n))
            (define-values (Vᵣ* φ*) (alloc-rest-args Σ ℓ H φ V-inits.rest #:end V-rest))
            ((apply-app-Ar C Vᵤ^ ctx) ℓ V-inits* Vᵣ* H φ Σ ⟦k⟧)])]
        [(-=> (? list? αℓₓs) _)
         (define n (length αℓₓs))
         (define num-remaining-args (- n num-inits))
         (cond
           [(>= num-remaining-args 0)
            (define pairs (unalloc-prefix σ (-φ-cache φ) V-rest num-remaining-args))
            (for/union : (℘ -ς) ([unalloced (in-set pairs)])
              (match-define (cons V-inits-more _) unalloced)
              (define V-inits* (append V-inits V-inits-more))
              ((app-Ar C Vᵤ^ ctx) ℓ V-inits* H φ Σ ⟦k⟧))]
           [else
            (error 'app/rest "expect ~a arguments, given ~a: ~a" n num-inits V-inits)])]
        [(-∀/C xs ⟦c⟧ ρ)
         (define l-seal (-ctx-neg ctx))
         (define-values (ρ* φ*)
           (for/fold ([ρ : -ρ ρ] [φ : -φ φ]) ([x (in-list xs)])
             (define αₛ (-α->⟪α⟫ (-α.imm (-Seal/C x H l-seal))))
             (define αᵥ (-α->⟪α⟫ (-α.sealed x H)))
             (values (ρ+ ρ x αₛ) (alloc Σ φ αᵥ ∅))))
         (define ⟦init⟧s : (Listof -⟦e⟧) (for/list ([V^ (in-list V-inits)]) (mk-A (list V^))))
         (define ⟦k⟧* (mon.v∷ ctx Vᵤ^ (ap∷ (list {set 'apply}) `(,@⟦init⟧s ,(mk-V V-rest)) ⊥ρ ℓ ⟦k⟧)))
         (⟦c⟧ ρ* H φ* Σ ⟦k⟧*)]
        [(-Case-> cases)
         (cond
           [(and (= 1 (set-count arg-counts)) (integer? (set-first arg-counts)))
            (define n (set-first arg-counts))
            (assert
             (for/or : (Option (℘ -ς)) ([C cases] #:when (arity-includes? (guard-arity C) n))
               (app-Ar/rest C α ctx)))]
           [else
            (for*/union : (℘ -ς) ([C cases]
                                  [a (in-value (guard-arity C))]
                                  #:when (for/or : Boolean ([argc (in-set arg-counts)])
                                           (arity-includes? a argc)))
              (app-Ar/rest C α ctx))])]))
    
    (match V-func
      [(-Clo xs ⟦e⟧ ρ) (app-clo/rest xs ⟦e⟧ ρ)]
      [(-Case-Clo cases)
       (define (go-case [clo : -Clo]) : (℘ -ς)
         (match-define (-Clo xs ⟦e⟧ ρ) clo)
         (app-clo/rest xs ⟦e⟧ ρ))
       (Cond
         [(and (= 1 (set-count arg-counts)) (integer? (set-first arg-counts)))
          (define n (set-first arg-counts))
          ;; already handled arity mismatch
          (assert
           (for/or : (Option (℘ -ς)) ([clo (in-list cases)]
                                      #:when (arity-includes? (assert (V-arity clo)) n))
             (go-case clo)))]
         [else
          (for*/union : (℘ -ς) ([clo (in-list cases)]
                                [a (in-value (assert (V-arity clo)))]
                                #:when (for/or : Boolean ([argc (in-set arg-counts)])
                                         (arity-includes? a argc)))
                      (go-case clo))])]
      [(-Ar C α ctx) (app-Ar/rest C α ctx)]
      [(? -o? o) (app-prim/rest o)]
      [_ (error 'app/rest "unhandled: ~a" (show-V V-func))]))
  |#

  (: ⟦F⟧->⟦F⟧^ : ⟦F⟧ → ⟦F⟧^)
  (define ((⟦F⟧->⟦F⟧^ ⟦F⟧) W ℓ Φ^ Ξ Σ) {set (⟦F⟧ W ℓ Φ^ Ξ Σ)})
  )
