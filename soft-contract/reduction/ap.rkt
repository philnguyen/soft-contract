#lang typed/racket/base

(provide ap ↝.@)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../delta.rkt"
         "helpers.rkt"
         "continuation-if.rkt")

(: ↝.@ : Mon-Party -ℓ (Listof -W¹) (Listof -⟦e⟧) → -⟦ℰ⟧)
(define (((↝.@ l ℓ Ws ⟦e⟧s) ⟦e⟧) M σ ℒ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.@ l ℓ Ws ℰ ⟦e⟧s))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 (l Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (define ℒ* (-ℒ-with-Γ ℒ Γ*))
        (match ⟦e⟧s ; TODO: move this dispatch out?
          ['()
           (match-define (cons Wₕ Wₓs) (reverse Ws*))
           ((ap l ℓ Wₕ Wₓs) M σ* ℒ*)]
          [(cons ⟦e⟧* ⟦e⟧s*)
           (((↝.@ l ℓ Ws* ⟦e⟧s*) ⟦e⟧*) M σ* ℒ*)]))))
   (⟦e⟧ M σ ℒ)))

;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define/memo (ap [l : Mon-Party] [ℓ : -ℓ] [Wₕ : -W¹] [Wₓs : (Listof -W¹)]) : -⟦e⟧
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ (apply -?@ sₕ sₓs))
  
  (λ (M σ ℒ₀)
    (match-define (-ℒ ρ₀ Γ₀ 𝒞₀) ℒ₀)

    ;; Make sure `Wₕ` handles the number of arguments passed
    (define-syntax-rule (with-guarded-arity a* e ...)
      (let ([n (length Wₓs)]
            [a a*])
        (cond
          [(arity-includes? a n) e ...]
          [else
           ;; HACK for error message, but probably no need for fix
           (define blm (-blm l 'Λ (list (format-symbol "~a values" a)) (list (-b n))))
           (values ⊥σ ∅ {set (-ΓE Γ₀ blm)} ∅)])))

    ;; Different handlers depending on the type of `Wₕ`.
    ;; Lots of free variables from above.

    (: ap/δ : Symbol → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    ;; Apply primitive
    (define (ap/δ o)
      (define-values (δσ A*) (δ 𝒞₀ ℓ M σ Γ₀ o Wₓs))
      (cond [(list? A*)
             (values δσ {set (-ΓW Γ₀ (-W A* sₐ))} ∅ ∅)]
            ;; Rely on `δ` giving no error
            [else (⊥ans)]))

    (: ap/β : -formals -⟦e⟧ -ρ -Γ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    ;; Apply λ abstraction
    (define (ap/β xs ⟦e⟧ ρ Γ₁)
      (define 𝒞₁ (𝒞+ 𝒞₀ (cons ⟦e⟧ ℓ)))
      (define-values (δσ ρ₁)
        (match xs
          [(? list? xs)
           (for/fold ([δσ : -Δσ ⊥σ] [ρ : -ρ ρ])
                     ([x xs] [V Vₓs])
             (define α (-α.x x 𝒞₁))
             (values (⊔ δσ α V) (ρ+ ρ x α)))]
          [_ (error 'ap/β "TODO: varargs")]))
      (define bnds (map (inst cons Symbol -s) xs sₓs))
      (define ℬ₁ (-ℬ ⟦e⟧ (-ℒ ρ₁ Γ₁ 𝒞₁)))
      (values δσ ∅ ∅ {set (-ℐ (-ℋ ℒ₀ sₕ bnds '□) ℬ₁)}))

    (: ap/Ar : -=>i -V -s Mon-Info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/Ar C Vᵤ sᵤ l³)
      (match-define (-=>i αs (-Clo xs ⟦r⟧ ρᵣ Γᵣ)) C)
      (for*/ans ([Cs (σ@/list σ αs)])
                ;; Monitor arguments
                ;; Compute range
                ;; Monitor result
                (error "TODO"))
      )

    (: ap/And/C : -W¹ -W¹ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/And/C WC₁ WC₂)
      (define ⟦e⟧₁ (ap l ℓ WC₁ Wₓs))
      (define ⟦e⟧₂ (ap l ℓ WC₂ Wₓs))
      (((↝.if l ⟦e⟧₂ ⟦ff⟧) ⟦e⟧₁) M σ ℒ₀))

    (: ap/Or/C : -W¹ -W¹ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/Or/C WC₁ WC₂)
      (define ⟦e⟧₁ (ap l ℓ WC₁ Wₓs))
      (define ⟦e⟧₂ (ap l ℓ WC₂ Wₓs))
      ;; FIXME not quite
      (((↝.if l ⟦tt⟧ ⟦e⟧₂) ⟦e⟧₁) M σ ℒ₀))

    (: ap/Not/C : -W¹ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/Not/C WC*)
      (define ⟦e⟧* (ap l ℓ WC* Wₓs))
      (((↝.@ l ℓ (list -not/W) '()) ⟦e⟧*) M σ ℒ₀))

    (: ap/contract-first-order-passes? : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/contract-first-order-passes?)
      (match-define (list WC WV) Wₓs)
      (error "TODO"))

    (: ap/st-p : -struct-info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-p s)
      (define ans
        (case (MσΓ⊢oW M σ Γ₀ (-st-p s) (car Wₓs))
          [(✓) (-ΓW (Γ+ Γ₀ sₐ)        (-W (list -tt) sₐ))]
          [(✗) (-ΓW (Γ+ Γ₀ (-not sₐ)) (-W (list -ff) sₐ))]
          [(?) (-ΓW     Γ₀            (-W -●/Vs      sₐ))]))
      (values ⊥σ {set ans} ∅ ∅))

    (: ap/st-mk : -struct-info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-mk s)
      (define αs : (Listof -α.fld)
        (for/list ([i : Natural (-struct-info-arity s)])
          (-α.fld ℓ 𝒞₀ i)))
      (define δσ
        (for/fold ([δσ : -Δσ ⊥σ])
                  ([α αs] [W Wₓs])
          (⊔ δσ α (-W¹-V W))))
      (define V (-St s αs))
      (values δσ {set (-ΓW Γ₀ (-W (list V) sₐ))} ∅ ∅))

    (: ap/st-ac : -struct-info Natural → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-ac s i)
      (define n (-struct-info-arity s))
      (match-define (list Wₓ) Wₓs)
      (match-define (-W¹ Vₓ sₓ) Wₓ)
      (match Vₓ
        [(-St (== s) αs)
         (define ans
           (for/set: : (℘ -ΓW) ([Vₐ (σ@ σ (list-ref αs i))])
             (-ΓW Γ₀ (-W (list Vₐ) sₐ))))
         (values ⊥σ ans ∅ ∅)]
        [(-St* (== s) _ _ _)
         (error 'struct-accesor "TODO: wrapped struct")]
        [(-●) ; error must have been catched from ouside. This is the unsafe version
         (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]
        [_ (⊥ans)]))

    (: ap/st-mut : -struct-info Natural → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-mut s i)
      (error '|struct mutator| "TODO"))

    (: ap/vector-ref : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/vector-ref)
      (error 'vector-ref "TODO"))

    (: ap/vector-set! : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/vector-set!)
      (error 'error-set! "TODO"))
    
    (match Vₕ
      
      ;; Struct operators cannot be handled by `δ`, because structs can be arbitrarily wrapped
      ;; by proxies, and contract checking is arbitrarily deep
      ;; Also, there's no need to check for preconditions, because they should have been caught
      ;; by wrapping contracts
      [(-st-p s)     (ap/st-p   s  )]
      [(-st-mk s)    (ap/st-mk  s  )]
      [(-st-ac s i)  (ap/st-ac  s i)]
      [(-st-mut s i) (ap/st-mut s i)]
      ['contract-first-order-passes? (ap/contract-first-order-passes?)]
      ['vector-ref  (ap/vector-ref )]
      ['vector-set! (ap/vector-set!)]
      
      ;; Regular stuff
      [(? symbol? o) (ap/δ o)]
      [(-Clo xs ⟦e⟧ ρ Γ)
       (with-guarded-arity (formals-arity xs)
         (ap/β xs ⟦e⟧ ρ Γ))]
      [(-Ar (? -=>i? C) (cons α fᵤ) l³)
       (with-guarded-arity (guard-arity C)
         (for*/ans ([Vᵤ (σ@ σ α)])
                   (ap/Ar C Vᵤ fᵤ l³)))]
      [(-And/C #t α₁ α₂)
       (with-guarded-arity 1
         (match-define (list c₁ c₂) (-app-split sₕ 'and/c 2))
         (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
                   (ap/And/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
      [(-Or/C #t α₁ α₂)
       (with-guarded-arity 1
         (match-define (list c₁ c₂) (-app-split sₕ 'or/c 2))
         (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
                   (ap/Or/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
      [(-Not/C α)
       (with-guarded-arity 1
         (match-define (list c*) (-app-split sₕ 'not/c 1))
         (for*/ans ([C* (σ@ σ α)])
                   (ap/Not/C (-W¹ C* c*))))]
      [(-St/C #t si αs)
       (error 'ap "St/C")]
      [(-●) ; FIXME havoc
       (printf "ap: ●~n")
       (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]
      [_ (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅)])))

