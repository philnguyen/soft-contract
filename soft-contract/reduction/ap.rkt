#lang typed/racket/base

(provide ap ↝.@ mon ↝.mon.c ↝.mon.v blm ↝.let-values ↝.letrec-values)

(require racket/match
         racket/set
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../delta.rkt"
         "helpers.rkt"
         "continuation-if.rkt"
         "continuation-amb.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: ↝.@ : Mon-Party -ℓ (Listof -W¹) (Listof -⟦e⟧) → -⟦ℰ⟧)
(define ((↝.@ l ℓ Ws ⟦e⟧s) ⟦e⟧)
  (define (ℰ+ [ℰ : -ℰ]) (-ℰ.@ l ℓ Ws ℰ ⟦e⟧s))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      ℰ+
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
     (⟦e⟧ M σ ℒ))))

;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define/memo (ap [l : Mon-Party] [ℓ : -ℓ] [Wₕ : -W¹] [Wₓs : (Listof -W¹)]) : -⟦e⟧
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ
    (let ([sₕ* (or sₕ
                   (match Vₕ
                     [(? -prim? o) o]
                     [(-Ar _ (-α.def (-𝒾 o 'Λ)) _) o]
                     [(-Ar _ (-α.wrp (-𝒾 o 'Λ)) _) o]
                     [_ #f]))])
      (apply -?@ sₕ* sₓs)))

  (: blm-arity : Arity Natural → -blm)
  (define (blm-arity required provided)
    ;; HACK for error message, but probably no need to fix
    (-blm l 'Λ (list (format-symbol "~a arguments" required)) (list (-b provided))))

  (λ (M σ ℒ₀)
    (match-define (-ℒ ρ₀ Γ₀ 𝒞₀) ℒ₀)

    #;(begin ; debugging
      (printf "About to apply ~a ~a -> ~a in ~a~n"
              (show-W¹ Wₕ)
              (map show-W¹ Wₓs)
              (show-s sₐ)
              (show-ℒ ℒ₀)))

    ;; Make sure `Wₕ` handles the number of arguments passed
    (define-syntax-rule (with-guarded-arity a* e ...)
      (let ([n (length Wₓs)]
            [a a*])
        (cond
          [(arity-includes? a n) e ...]
          [else (values ⊥σ ∅ {set (-ΓE Γ₀ (blm-arity a n))} ∅)])))

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
      (define bnds (map (inst cons Var-Name -s) xs sₓs))
      (define ℬ₁ (-ℬ ⟦e⟧ (-ℒ ρ₁ Γ₁ 𝒞₁)))
      (values δσ ∅ ∅ {set (-ℐ (-ℋ ℒ₀ sₕ bnds '□) ℬ₁)}))

    (: ap/Ar : -=> -V Mon-Info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/Ar C Vᵤ l³)
      (match-define (Mon-Info l+ l- lo) l³)
      (define l³* (Mon-Info l- l+ lo))
      (define Wᵤ (-W¹ Vᵤ sₕ)) ;; Inner function
      (match-define (-=> αs β) C)
      (define cs : (Listof -s) (for/list ([α αs]) (and (-e? α) α)))
      (define d (and (-e? β) β))
      
      (match αs
        ['() ; no arg
         (define ⟦ap⟧ : -⟦e⟧ (ap lo ℓ Wᵤ '()))
         (for*/ans ([D (σ@ σ β)])
           (((↝.mon.c l³ ℓ (-W¹ D d)) ⟦ap⟧) M σ ℒ₀))]
        [(cons α αs*)
         (for*/ans ([Cs (σ@/list σ αs)])
           (match-define (cons ⟦mon-x⟧ ⟦mon-x⟧s)
             (for/list : (Listof -⟦e⟧) ([C Cs] [c cs] [Wₓ Wₓs])
               (mon l³* ℓ (-W¹ C c) Wₓ)))
           (define ⟦ap⟧ : -⟦e⟧ ((↝.@ lo ℓ (list Wᵤ) ⟦mon-x⟧s) ⟦mon-x⟧))
           (for*/ans ([D (σ@ σ β)])
             (define comp : -⟦e⟧ ((↝.mon.c l³ ℓ (-W¹ D d)) ⟦ap⟧))
             (comp M σ ℒ₀)))]))

    (: ap/indy : -=>i -V Mon-Info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/indy C Vᵤ l³)
      (match-define (Mon-Info l+ l- lo) l³)
      (define l³* (Mon-Info l- l+ lo))
      (define Wᵤ    (-W¹ Vᵤ   sₕ)) ;; Inner function
      (match-define (-=>i αs γ) C)
      (define cs : (Listof -s) (for/list ([α αs]) (and (-e? α) α)))
      (define mk-d (and (-e? γ) γ))

      (for*/ans ([Mk-D (σ@ σ γ)])
        (match-define (-Clo xs _ _ _) Mk-D)
        (define W-rng (-W¹ Mk-D mk-d))
        (match xs
          [(? list? xs)
           (define xs⇓ (map ⇓ₓ xs))
           (for*/ans ([Cs (σ@/list σ αs)])
              ;; TODO: make sure it's ok to reuse variables `xs`
                     
              ;; Monitor arguments
              (define ⟦mon-x⟧s : (Listof -⟦e⟧)
                (for/list ([C Cs] [c cs] [Wₓ Wₓs])
                  (mon l³* ℓ (-W¹ C c) Wₓ)))
              
              ;; TODO: make sure it's ok to not memoize these run-time generated computations
              (define comp
                (match* (xs xs⇓ ⟦mon-x⟧s)
                  [('() '() '()) ; 0-arg
                   (define ⟦mk-d⟧ : -⟦e⟧ (ap lo ℓ W-rng '()))
                   (define ⟦ap⟧   : -⟦e⟧ (ap lo ℓ Wᵤ    '()))
                   ((↝.mon.v l³ ℓ ⟦ap⟧) ⟦mk-d⟧)]
                  [((cons x xs*) (cons x⇓ xs⇓*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
                   (define ⟦mon-y⟧ : -⟦e⟧
                     (let ([⟦mk-d⟧ : -⟦e⟧ ((↝.@ lo ℓ (list W-rng) xs⇓*) x⇓)]
                           [⟦ap⟧   : -⟦e⟧ ((↝.@ lo ℓ (list Wᵤ   ) xs⇓*) x⇓)])
                       ((↝.mon.v l³ ℓ ⟦ap⟧) ⟦mk-d⟧)))
                   (define bnds : (Listof (Pairof (Listof Var-Name) -⟦e⟧))
                     (for/list ([xᵢ xs*] [⟦mon-xᵢ⟧ ⟦mon-x⟧s*])
                       (cons (list xᵢ) ⟦mon-xᵢ⟧)))
                   ((↝.let-values lo '() (list x) bnds ⟦mon-y⟧) ⟦mon-x⟧)]))
              (comp M σ ℒ₀))]
          [(-varargs zs z)
           (error 'ap "Apply variable arity arrow")])))

    (: ap/case : -Case-> -V Mon-Info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/case C Vᵤ l³)
      (error 'ap/case "TODO"))

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
      (error 'contract-first-order-passes? "TODO"))

    (: ap/st-p : -struct-info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-p s)
      (define ans
        (case (MσΓ⊢oW M σ Γ₀ (-st-p s) (car Wₓs))
          [(✓) (-ΓW (Γ+ Γ₀ sₐ)        (-W -True/Vs  sₐ))]
          [(✗) (-ΓW (Γ+ Γ₀ (-not sₐ)) (-W -False/Vs sₐ))]
          [(?) (-ΓW     Γ₀            (-W -●/Vs     sₐ))]))
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
         (error 'struct-accessor "TODO: wrapped struct")]
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

    (: ap/● : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/●)
      (define havoc-𝒾 (-𝒾 'havoc-id 'havoc))
      (define Wₕᵥ (-W¹ (σ@¹ σ (-α.def havoc-𝒾)) (-ref havoc-𝒾 0)))
      (⊔/ans (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)
             (for*/ans ([Wₓ Wₓs])
               ((ap 'Λ ℓ Wₕᵥ (list Wₓ)) M σ ℒ₀))))
    (define-values (a b c d) (match Vₕ
      
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
      [(-Case-Clo clauses ρ Γ)
       (define n (length Wₓs))
       (define clause
         (for/or : (Option (Pairof (Listof Var-Name) -⟦e⟧)) ([clause clauses])
           (match-define (cons xs _) clause)
           (and (equal? n (length xs)) clause)))
       (cond
         [clause
          (match-define (cons xs ⟦e⟧) clause)
          (ap/β xs ⟦e⟧ ρ Γ)]
         [else
          (define a (assert (V-arity Vₕ)))
          (values ⊥σ ∅ {set (-ΓE Γ₀ (blm-arity a n))} ∅)])]
      [(-Ar C α l³)
       (with-guarded-arity (guard-arity C)
         (cond [(-=>? C)  (for*/ans ([Vᵤ (σ@ σ α)]) (ap/Ar   C Vᵤ l³))]
               [(-=>i? C) (for*/ans ([Vᵤ (σ@ σ α)]) (ap/indy C Vᵤ l³))]
               [else      (for*/ans ([Vᵤ (σ@ σ α)]) (ap/case C Vᵤ l³))]))]
      [(-And/C #t α₁ α₂)
       (with-guarded-arity 1
         (define-values (c₁ c₂)
           (match-let ([(list s₁ s₂) (-app-split sₕ 'and/c 2)])
             (values (or s₁ (and (-e? α₁) α₁))
                     (or s₂ (and (-e? α₂) α₂)))))
         (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
                   (ap/And/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
      [(-Or/C #t α₁ α₂)
       (with-guarded-arity 1
         (define-values (c₁ c₂)
           (match-let ([(list s₁ s₂) (-app-split sₕ 'or/c 2)])
             (values (or s₁ (and (-e? α₁) α₁))
                     (or s₂ (and (-e? α₂) α₂)))))
         (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
                   (ap/Or/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
      [(-Not/C α)
       (with-guarded-arity 1
         (define c*
           (match-let ([(list s) (-app-split sₕ 'not/c 1)])
             (or s (and (-e? α) α))))
         (for*/ans ([C* (σ@ σ α)])
                   (ap/Not/C (-W¹ C* c*))))]
      [(-St/C #t si αs)
       (error 'ap "St/C")]
      [(-●) (ap/●)]
      [_ (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅)]))
    ;(printf "Ap: ~a ~a --> ~a | ~a~n" (show-W¹ Wₕ) (map show-W¹ Wₓs) (set-map b show-A) (set-map d show-ℐ))
    (values a b c d)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Contract monitoring
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Monitor contract.
(define/memo (mon [l³ : Mon-Info] [ℓ : -ℓ] [W-C : -W¹] [W-V : -W¹]) : -⟦e⟧
  (match-define (-W¹ C _) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (define mon*
    (cond
      [(-=>_? C)      mon-=>_     ]
      [(-St/C? C)     mon-struct/c]
      [(-x/C? C)      mon-x/c     ]
      [(-And/C? C)    mon-and/c   ]
      [(-Or/C?  C)    mon-or/c    ]
      [(-Not/C? C)    mon-not/c   ]
      [(-Vectorof? C) mon-vectorof]
      [(-Vector/C? C) mon-vector/c]
      [else           mon-flat    ]))

  (λ (M σ ℒ)
    (define Γ (-ℒ-cnd ℒ))
    (case (MσΓ⊢V∈C M σ Γ W-V W-C)
      [(✓)
       (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅)]
      [(✗)
       (values ⊥σ ∅ {set (-ΓE (-ℒ-cnd ℒ) (-blm l+ lo (list C) (list V)))} ∅)]
      [(?)
       ((mon* l³ ℓ W-C W-V) M σ ℒ)])))

(: mon-=>_ : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-=>_ l³ ℓ W-C W-V)
  (match-define (-W¹ grd c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  
  (define arity
    (let ([a
           (match grd
             [(-=> αs _) (length αs)]
             [(-=>i _ β)
              (match β
                [(-λ xs _) (formals-arity xs)]
                [_ #f])])])
      (define b (-b a))
      (-W¹ b b)))
  
  (λ (M σ ℒ)
    ;; Perform first-order checks for procedure?-ness and arity before wrapping
    (define Γ (-ℒ-cnd ℒ))
    (define-values (Γ₁ Γ₂) (Γ+/-W∋Ws M σ Γ -procedure?/W W-V))
    (define-values (Γ₁₁ Γ₁₂)
      (if Γ₁
          (let ([A (V-arity V)]
                [a (-?@ 'procedure-arity v)])
            (define W-a (-W¹ (if A (-b A) -●/V) a))
            (Γ+/-W∋Ws M σ Γ₁ -arity-includes?/W W-a arity))
          (values #f #f)))
    (define-set ΓWs : -ΓW)
    (define-set ΓEs : -ΓE)
    (define δσ : -Δσ ⊥σ)
    (when Γ₁₁
      (define α (-α.rng ℓ (-ℒ-hist ℒ)))
      (define Ar (-Ar grd α l³))
      (ΓWs-add! (-ΓW Γ₁₁ (-W (list Ar) v)))
      (set! δσ (⊔ ⊥σ α V)))
    (when Γ₁₂
      (define C #|HACK|#
        (match arity
          [(-W¹ (-b (? integer? n)) _)
           (format-symbol "(arity-includes/c ~a)" n)]
          [(-W¹ (-b (arity-at-least n)) _)
           (format-symbol "(arity-at-least/c ~a)" n)]))
      (ΓEs-add! (-ΓE Γ₁₂ (-blm l+ lo (list C) (list V)))))
    (when Γ₂
      (ΓEs-add! (-ΓE Γ₂ (-blm l+ lo (list 'procedure?) (list V)))))
    (values δσ ΓWs ΓEs ∅)))

(: mon-struct/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-struct/c l³ ℓ W-C W-V)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-St/C flat? s αs) C)
  (define cs (-struct/c-split c (-struct-info-arity s)))
  
  (define ⟦field⟧s : (Listof -⟦e⟧)
    (for/list ([(α i) (in-indexed αs)])
      (define ac (-st-ac s (assert i exact-nonnegative-integer?)))
      (ap lo ℓ (-W¹ ac ac) (list (-W¹ V v)))))
  
  (match V
    [(or (-St (== s) _) (-St* (== s) _ _ _))
     (λ (M σ ℒ)
       (for*/ans ([Cs (σ@/list σ αs)])
         (define ⟦mon-field⟧s : (Listof -⟦e⟧)
           (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s])
             ((↝.mon.c l³ ℓ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
         (define comp : -⟦e⟧
           (match ⟦mon-field⟧s
             ['()
              (λ (M σ ℒ)
                (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅))]
             [(cons ⟦mon-field⟧ ⟦mon-field⟧s*)
              (define k (-st-mk s))
              ((↝.@ lo ℓ (list (-W¹ k k)) ⟦mon-field⟧s*) ⟦mon-field⟧)]))
         (comp M σ ℒ)))]
    [(-●)
     (define p (-st-p s))
     (λ (M σ ℒ)
       (for*/ans ([Cs (σ@/list σ αs)])
         (define ⟦blm⟧ (blm l+ lo (list (-st-p s)) (list V)))
         (define ⟦mon-field⟧s : (Listof -⟦e⟧)
           (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s])
             ((↝.mon.c l³ ℓ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
         (define ⟦mk⟧ : -⟦e⟧
           (match ⟦mon-field⟧s
             ['()
              (λ (M σ ℒ)
                (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅))]
             [(cons ⟦mon-field⟧ ⟦mon-field⟧s*)
              (define k (-st-mk s))
              ((↝.@ lo ℓ (list (-W¹ k k)) ⟦mon-field⟧s*) ⟦mon-field⟧)]))
         (define comp
           ((↝.if lo ⟦mk⟧ ⟦blm⟧) (ap lo ℓ (-W¹ p p) (list W-V))))
         (comp M σ ℒ)))]
    [_ (blm l+ lo (list C) (list V))]))

(: mon-x/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-x/c l³ ℓ W-C W-V)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-x/C α) C)
  
  (match V
    [(-●)
     (λ (M σ ℒ)
       (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅))]
    [_
     (λ (M σ ℒ)
       (for*/ans ([C* (σ@ σ α)])
         (define W-C* (-W¹ C* c))
         (values ⊥σ ∅ ∅ {set (-ℐ (-ℋ ℒ #f '() '□) (-ℳ l³ ℓ W-C* W-V ℒ))})))]))

(: mon-and/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
;; Monitor contract conjunction by decomposing into nesting checks
(define (mon-and/c l³ ℓ W-C W-V)
  (match-define (-W¹ (-And/C _ α₁ α₂) c) W-C)
  (match-define (list c₁ c₂) (-app-split c 'and/c 2))
  (λ (M σ ℒ)
    (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       ;; TODO: be careful `(mon ...)` can generate infinitely many ⟦e⟧s
       (((↝.mon.c l³ ℓ (-W¹ C₂ c₂)) (mon l³ ℓ (-W¹ C₁ c₁) W-V)) M σ ℒ))))

(: mon-or/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-or/c l³ ℓ W-C W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ (-Or/C flat? α₁ α₂) c) W-C)
  (define-values (c₁ c₂)
    (match-let ([(list s₁ s₂) (-app-split c 'or/c 2)])
      (values (or s₁ (and (-e? α₁) α₁))
              (or s₂ (and (-e? α₂) α₂)))))
  (define ⟦ok⟧ (ret-W¹ W-V))
  (λ (M σ ℒ)
    (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
      (cond
        [(C-flat? C₁)
         (define ⟦chk⟧ (ap lo ℓ (-W¹ C₁ c₁) (list W-V)))
         (define ⟦mon⟧ (mon l³ ℓ (-W¹ C₂ c₂) W-V))
         (((↝.if lo ⟦ok⟧ ⟦mon⟧) ⟦chk⟧) M σ ℒ)]
        [(C-flat? C₂)
         (define ⟦chk⟧ (ap lo ℓ (-W¹ C₂ c₂) (list W-V)))
         (define ⟦mon⟧ (mon l³ ℓ (-W¹ C₁ c₁) W-V))
         (((↝.if lo ⟦ok⟧ ⟦mon⟧) ⟦chk⟧) M σ ℒ)]
        [else ; both are chaperones, error for now (TODO: real semantics: distinguish by 1st order)
         (error 'or/c "No more than 1 higher-order disjunct for now")]))))

(: mon-not/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
;; Monitor negation contract. It must be flat.
(define (mon-not/c l³ ℓ W-C W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ (and C (-Not/C α)) c) W-C)
  (match-define (-W¹ V _) W-V)
  (match-define (list c*) (-app-split c 'not/c 1))
  (define ⟦ℰ⟧
    (let ([⟦e⟧ₒₖ (ret-W¹ W-V)]
          [⟦e⟧ₑᵣ (blm l+ lo (list C) (list V))])
      (↝.if lo ⟦e⟧ₑᵣ ⟦e⟧ₒₖ)))
  (λ (M σ ℒ)
    (for*/ans ([C* (σ@ σ α)])
      (assert C* C-flat?)
      (define W-C* (-W¹ C* c*))
      ((⟦ℰ⟧ (ap lo 0 W-C* (list W-V))) M σ ℒ))))

(: mon-vectorof : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-vectorof l³ ℓ α V)
  (error 'mon-vectorof "TODO"))

(: mon-vector/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-vector/c l³ ℓ αs V)
  (error 'mon-vector/c "TODO"))

(: mon-flat : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
;; Monitor flat contract
(define (mon-flat l³ ℓ W-C W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ C _) W-C)
  (match-define (-W¹ V _) W-V)
  (define ⟦ℰ⟧
    (let ([⟦e⟧ₒₖ (ret-W¹ W-V)]
          [⟦e⟧ₑᵣ (blm l+ lo (list C) (list V))])
      (↝.if lo ⟦e⟧ₒₖ ⟦e⟧ₑᵣ)))
  (⟦ℰ⟧ (ap lo 0 W-C (list W-V))))

(: ↝.mon.v : Mon-Info -ℓ (U -⟦e⟧ -W¹) → -⟦ℰ⟧)
;; Waiting on contract to monitor
(define ((↝.mon.v l³ ℓ Val) ⟦c⟧)
  (define lo (Mon-Info-src l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.mon.v l³ ℓ ℰ Val))
      (λ (σ* Γ* W)
        (match-define (-W Vs c) W)
        (with-guarded-arity 1 (lo Γ* Vs)
          (match-define (list C) Vs)
          (define W-C (-W¹ C c))
          ;; If target is evaluated, check it, otherwise evaluate it before checking
          (define ⟦mon⟧
            (cond [(-W¹? Val) (   mon   l³ ℓ W-C  Val)]
                  [else       ((↝.mon.c l³ ℓ W-C) Val)]))
          (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))
     (⟦c⟧ M σ ℒ))))

(: ↝.mon.c : Mon-Info -ℓ (U -⟦e⟧ -W¹) → -⟦ℰ⟧)
;; Waiting on value to monitor
(define ((↝.mon.c l³ ℓ Ctc) ⟦e⟧)
  (define lo (Mon-Info-src l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.mon.c l³ ℓ Ctc ℰ))
      (λ (σ* Γ* W)
        (match-define (-W Vs v) W)
        (with-guarded-arity 1 (lo Γ* Vs)
          (match-define (list V) Vs)
          (define W-V (-W¹ V v))
          ;; If contract is evaluated, check with it, otherwise evaluate it before checking
          (define ⟦mon⟧
            (cond [(-W¹? Ctc) (   mon   l³ ℓ Ctc  W-V)]
                  [else       ((↝.mon.v l³ ℓ W-V) Ctc)]))
          (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))
     (⟦e⟧ M σ ℒ))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Let-binding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: ↝.let-values : Mon-Party
                  (Listof (Pairof Var-Name -W¹))
                  (Listof Var-Name)
                  (Listof (Pairof (Listof Var-Name) -⟦e⟧))
                  -⟦e⟧
                  → -⟦ℰ⟧)
(define (((↝.let-values l x-Ws xs xs-⟦e⟧s ⟦e⟧) ⟦eₓ⟧) M σ ℒ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.let-values l x-Ws (cons xs ℰ) xs-⟦e⟧s ⟦e⟧))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (define n (length xs))
      (with-guarded-arity n (l Γ* Vs)
        (define x-Ws*
          (foldr
           (λ ([x : Var-Name] [V : -V] [s : -s] [x-Ws* : (Listof (Pairof Var-Name -W¹))])
             (cons (cons x (-W¹ V s)) x-Ws*))
           x-Ws
           xs
           Vs
           (split-values s n)))
        (match xs-⟦e⟧s ; TODO dispatch outside?
          ['()
           (match-define (-ℒ ρ _ 𝒞) ℒ)
           (define-values (ρ* δσ Γ**)
             (for/fold ([ρ* : -ρ ρ] [δσ : -Δσ ⊥σ] [Γ** : -Γ Γ*])
                       ([x-W x-Ws*])
               (match-define (cons x (-W¹ V s)) x-W)
               (define α (-α.x x 𝒞))
               (values (hash-set ρ* x α)
                       (⊔ δσ α V)
                       (-Γ-with-aliases Γ* x s))))
           (define σ** (⊔/m σ* δσ))
           (⊔/ans (values δσ ∅ ∅ ∅)
                  (⟦e⟧ M σ** (-ℒ ρ* Γ** 𝒞)))]
          [(cons (cons xs* ⟦e⟧*) xs-⟦e⟧s*)
           (((↝.let-values l x-Ws* xs* xs-⟦e⟧s* ⟦e⟧) ⟦e⟧*) M σ* (-ℒ-with-Γ ℒ Γ*))]
          ))))
   (⟦eₓ⟧ M σ ℒ)))

(: ↝.letrec-values : Mon-Party
                     -Δρ
                     (Listof Var-Name)
                     (Listof (Pairof (Listof Var-Name) -⟦e⟧))
                     -⟦e⟧
                     → -⟦ℰ⟧)
(define (((↝.letrec-values l δρ xs xs-⟦e⟧s ⟦e⟧) ⟦eₓ⟧) M σ ℒ)
  ;; FIXME: inefficient. `ρ*` is recomputed many times
  (define ρ (-ℒ-env ℒ))
  (define ℒ* (-ℒ-with-ρ ℒ (ρ++ ρ δρ)))
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.letrec-values l δρ (cons xs ℰ) xs-⟦e⟧s ⟦e⟧))
    (λ (σ₀ Γ₀ W)
      (define n (length xs))
      (match-define (-W Vs s) W)
      (with-guarded-arity n (l Γ₀ Vs)
        ;; Update/widen store and path condition
        (define-values (δσ Γ₁)
          (for/fold ([δσ : -Δσ ⊥σ] [Γ₁ : -Γ Γ₀])
                    ([x xs] [V Vs] [sₓ (split-values s n)])
            (values (⊔ δσ (ρ@ δρ x) V)
                    (Γ+ (if sₓ (-Γ-with-aliases Γ₁ x sₓ) Γ₁) (-?@ 'defined? (-x x))))))
        (define σ₁ (⊔/m σ₀ δσ))
        
        (match xs-⟦e⟧s
          [(cons (cons xs* ⟦e⟧*) xs-⟦e⟧s*)
           (⊔/ans
             (values δσ ∅ ∅ ∅)
             (((↝.letrec-values l δρ xs* xs-⟦e⟧s* ⟦e⟧) ⟦e⟧*) M σ₁ (-ℒ-with-Γ ℒ Γ₁)))]
          ['()
           (define-values (δσ* ΓWs ΓEs ℐs) (⟦e⟧ M σ (-ℒ-with-Γ ℒ* Γ₁)))
           
           ;;; Erase irrelevant part of path conditions after executing letrec body

           ;; Free variables that outside of `letrec` understands
           (define xs₀ (list->set (hash-keys ρ)))

           (define ΓWs*
             (map/set
              (match-lambda
                [(-ΓW Γ (-W Vs s))
                 (-ΓW (Γ↓ Γ xs₀) (-W Vs (s↓ s xs₀)))])
              ΓWs))
           
           (define ΓEs*
             (map/set
              (match-lambda
                [(-ΓE Γ blm)
                 (-ΓE (Γ↓ Γ xs₀) blm)])
              ΓEs))
           
           (define ℐs*
             (map/set
              (match-lambda
                [(-ℐ (-ℋ ℒ f bnds ℰ) τ)
                 (define Γ* (Γ↓ (-ℒ-cnd ℒ) xs₀))
                 (define f* (s↓ f xs₀))
                 (define bnds*
                   (for/list : (Listof (Pairof Var-Name -s)) ([bnd bnds])
                     (match-define (cons x s) bnd)
                     (cons x (s↓ s xs₀))))
                 (-ℐ (-ℋ (-ℒ-with-Γ ℒ Γ*) f* bnds* ℰ) τ)])
              ℐs))
           
           (values (⊔/m δσ δσ*) ΓWs* ΓEs* ℐs*)]))))
   (⟦eₓ⟧ M σ ℒ*)))


;; memoize these to avoid generating infinitely many compiled expressions
(define/memo (blm [l+ : Mon-Party] [lo : Mon-Party]
                  [Cs : (Listof -V)] [Vs : (Listof -V)]) : -⟦e⟧
  (case l+ ; ignore blames on system, top-level, and havoc
    [(Λ † havoc)
     ⊥⟦e⟧]
    [else
     (λ (M σ ℒ)
       (values ⊥σ ∅ {set (-ΓE (-ℒ-cnd ℒ) (-blm l+ lo Cs Vs))} ∅))]))

