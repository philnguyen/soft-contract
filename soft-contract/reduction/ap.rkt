#lang typed/racket/base

(provide ap ↝.@ mon ↝.mon.c ↝.mon.v blm ↝.let-values ↝.letrec-values)

(require racket/match
         racket/set
         (except-in racket/function arity-includes?)
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../delta.rkt"
         "helpers.rkt"
         "continuation-if.rkt"
         "continuation-amb.rkt"
         "continuation-begin.rkt"
         "wrap.rkt")


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
    (define msg : Symbol
      (cond
        [sₕ (format-symbol "~a requires ~a arguments" (show-e sₕ) required)]
        [else (format-symbol "require ~a arguments" required)]))
    (-blm l 'Λ (list msg) Vₓs))

  (λ (M σ ℒ₀)
    (match-define (-ℒ ρ₀ Γ₀ 𝒞₀) ℒ₀)

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
      (define bnd
        (let* ([fvs
                ;; It is important to take *all* of the caller's inscope variables,
                ;; rather than the invoked lambda's free variables.
                ;; Due to `canonicalize`, a refinement inside the closure
                ;; may refer to a variable not (directly) in the callee's scope
                (if (-λ? sₕ) (list->set (hash-keys ρ₀)) ∅)]
               [param->arg
                (for/hash : (HashTable Var-Name -e) ([x (assert xs list?)] [sₓ sₓs] #:when sₓ)
                  (values x sₓ))]
               [mapping
                (for/fold ([mapping : (HashTable Var-Name -e) param->arg]) ([x fvs])
                  ;(assert (not (hash-has-key? mapping x))) ; FIXME is this neccessary?
                  (hash-set mapping x (canonicalize Γ₀ x)))])
          (-binding sₕ xs mapping)))
      (values δσ ∅ ∅ {set (-ℐ (-ℋ ℒ₀ bnd '□) ℬ₁)}))

    (: ap/Ar : -=> -V Mon-Info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/Ar C Vᵤ l³)
      (match-define (Mon-Info l+ l- lo) l³)
      (define l³* (Mon-Info l- l+ lo))
      (define Wᵤ (-W¹ Vᵤ sₕ)) ;; Inner function
      (match-define (-=> αs β _) C)
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
      (match-define (-=>i αs γ _) C)
      (define cs : (Listof -s) (for/list ([α αs]) (and (-e? α) α)))
      (define mk-d (and (-λ? γ) γ))

      (for*/ans ([Mk-D (σ@ σ γ)])
        (match-define (-Clo xs _ _ _) Mk-D)
        (define W-rng (-W¹ Mk-D mk-d))
        (match xs
          [(? list? xs)
           (define xs⇓ (map (curry ⇓ₓ lo) xs))
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
    ;; Apply function wrapped in `case->`
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

    (: ap/St/C : -struct-info (Listof -W¹) → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/St/C s W-Cs)
      (match-define (list Wₓ) Wₓs)
      (match-define (-W¹ Vₓ _) Wₓ)
      (match Vₓ
        [(or (-St (== s) _) (-St* (== s) _ _ _) (-St● (== s)) (-● _))
         (define ⟦chk-field⟧s : (Listof -⟦e⟧)
           (for/list ([(W-C i) (in-indexed W-Cs)])
             (define Ac
               (let ([ac (-st-ac s (assert i exact-nonnegative-integer?))])
                 (-W¹ ac ac)))
             ((↝.@ l ℓ (list W-C) '()) (ap l ℓ Ac (list Wₓ)))))
         (define P (let ([p (-st-p s)]) (-W¹ p p)))
         (define comp ((↝.and l ⟦chk-field⟧s) (ap l ℓ P (list Wₓ))))
         (comp M σ ℒ₀)]
        [_
         (values ⊥σ {set (-ΓW Γ₀ (-W -False/Vs -ff))} ∅ ∅)]))

    (: ap/contract-first-order-passes? : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/contract-first-order-passes?)
      (match-define (list WC WV) Wₓs)
      (error 'contract-first-order-passes? "TODO"))

    (: ap/st-p : -struct-info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-p s)
      (define ans
        (case (MΓ⊢oW M Γ₀ (-st-p s) (car Wₓs))
          [(✓) (-ΓW (Γ+ Γ₀ sₐ)        (-W -True/Vs  sₐ))]
          [(✗) (-ΓW (Γ+ Γ₀ (-not sₐ)) (-W -False/Vs sₐ))]
          [(?) (-ΓW     Γ₀            (-W -Bool/Vs  sₐ))]))
      (values ⊥σ {set ans} ∅ ∅))

    (: ap/st-mk : -struct-info → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-mk s)
      (define 𝒾 (-struct-info-id s))
      (define αs : (Listof -α.fld)
        (for/list ([i : Natural (-struct-info-arity s)])
          (-α.fld 𝒾 ℓ 𝒞₀ i)))
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
      (define ac (-st-ac s i))
      (define p (-st-p s))
      (match Vₓ
        [(-St (== s) αs)
         (define ans
           (for/set: : (℘ -ΓW) ([Vₐ (σ@ σ (list-ref αs i))])
             (-ΓW Γ₀ (-W (list Vₐ) sₐ))))
         (values ⊥σ ans ∅ ∅)]
        [(-St* (== s) αs α l³)
         (match-define (Mon-Info _ _ lo) l³)
         (define Ac (-W¹ ac ac))
         (cond
           [(list-ref αs i) =>
            (λ ([γ : -α])
              (define c (and (-e? γ) γ))
              (for*/ans ([C (σ@ σ γ)] [Vₓ* (σ@ σ α)])
                 (define W-c (-W¹ C c))
                 (((↝.mon.c l³ ℓ W-c) (ap lo ℓ Ac (list (-W¹ Vₓ* sₓ)))) M σ ℒ₀)))]
           [else
            (for*/ans ([Vₓ* (σ@ σ α)])
              ((ap lo ℓ Ac (list (-W¹ Vₓ* sₓ))) M σ ℒ₀))])]
        [(-St● (== s))
         (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]
        [(-● _)
         (define ⟦ok⟧ : -⟦e⟧
           (λ (M σ ℒ)
             (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W -●/Vs sₐ))} ∅ ∅)))
         (define ⟦er⟧ : -⟦e⟧ (blm l (show-o ac) (list p) (list Vₓ)))
         (define comp ((↝.if 'Λ ⟦ok⟧ ⟦er⟧) (ap 'Λ ℓ (-W¹ p p) (list Wₓ))))
         (comp M σ ℒ₀)]
        [_
         (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l (show-o ac) (list p) (list Vₓ)))} ∅)]))

    (: ap/st-mut : -struct-info Natural → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/st-mut s i)
      (match-define (list Wₛ Wᵥ) Wₓs)
      (match-define (-W¹ Vₛ sₛ) Wₛ)
      (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
      (define mut (-st-mut s i))
      (define p (-st-p s))
      (match Vᵥ
        [(-St (== s) αs)
         (define α (list-ref αs i))
         (values (⊔ σ α Vᵥ) {set (-ΓW Γ₀ -Void/W)} ∅ ∅)]
        [(-St* (== s) γs α l³)
         (match-define (Mon-Info l+ l- lo) l³)
         (define l³* (Mon-Info l- l+ lo))
         (match-define (? -α? γ) (list-ref γs i))
         (define c (and (-e? γ) γ))
         (define Mut (-W¹ mut mut))
         (for*/ans ([C (σ@ σ γ)] [Vₛ* (σ@ σ α)])
           (define W-c (-W¹ C c))
           (define Wₛ* (-W¹ Vₛ* sₛ))
           (define ⟦chk⟧ (mon l³* ℓ W-c Wᵥ))
           (define comp ((↝.@ lo ℓ (list Wₛ* Mut) '()) ⟦chk⟧))
           (comp M σ ℒ₀))]
        [(-St● (== s))
         (values ⊥σ {set (-ΓW Γ₀ -Void/W)} ∅ ∅)]
        [(-● _)
         (define p (-st-p s))
         (define ⟦ok⟧ : -⟦e⟧ ; TODO havoc
           (let* ([Wₕᵥ (-W¹ (σ@¹ σ (-α.def havoc-𝒾)) havoc-𝒾)]
                  [⟦hv⟧ (ap havoc-path ℓ Wₕᵥ (list Wᵥ))])
             (⊔/⟦e⟧ ((↝.begin (list ⟦void⟧)) ⟦hv⟧)
                    ⟦void⟧)))
         (define ⟦er⟧ : -⟦e⟧ (blm l (show-o mut) (list p) (list Vₛ)))
         (define comp ((↝.if 'Λ ⟦ok⟧ ⟦er⟧) (ap 'Λ ℓ (-W¹ p p) (list Wₛ))))
         (comp M σ ℒ₀)]
        [_
         (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l (show-o mut) (list p) (list Vₛ)))} ∅)]))

    (: ap/unsafe-struct-ref : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/unsafe-struct-ref)
      (match-define (list Wᵥ Wᵢ) Wₓs)
      (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
      (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
      (match Vᵥ ; FIXME this implementation assumes no user program calls unsafe-struct-ref
        [(-St (-struct-info _ n _) αs)
         (for*/ans ([(α i) (in-indexed αs)]
                    #:when (exact-nonnegative-integer? i) ; hack for TR
                    #:when (plausible-index? M Γ₀ Wᵢ i)
                    [Γ* (in-value (Γ+ Γ₀ (-?@ '= sᵢ (-b i))))]
                    [V (σ@ σ α)])
           (values ⊥σ {set (-ΓW Γ* (-W (list V) sₐ))} ∅ ∅))]
        [(-St* (-struct-info _ n _) γs α l³)
         (match-define (Mon-Info _ _ lo) l³)
         (for*/ans ([(γ i) (in-indexed γs)]
                    #:when (exact-nonnegative-integer? i) ; hack for TR
                    #:when (plausible-index? M Γ₀ Wᵢ i)
                    [Γ* (in-value (Γ+ Γ₀ (-?@ '= sᵢ (-b i))))]
                    [c (in-value (and (-e? γ) γ))]
                    [V (σ@ σ α)]
                    [C (if γ (σ@ σ γ) {set #f})])
            (define comp
              (cond
                [C
                 (define W-c (-W¹ C c))
                 ((↝.mon.c l³ ℓ W-c) (ap lo ℓ -unsafe-struct-ref/W (list (-W¹ V sᵥ))))]
                [else
                 (ap lo ℓ -unsafe-struct-ref/W (list (-W¹ V sᵥ)))]))
            (comp M σ (-ℒ-with-Γ ℒ₀ Γ*)))]
        [(-St● _)
         (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]
        [_ (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]))
    
    (: ap/unsafe-struct-set! : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/unsafe-struct-set!)
      (error 'ap/unsafe-struct-set! "TODO"))

    (: ap/vector-ref : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/vector-ref)
      (match-define (list Wᵥ Wᵢ) Wₓs)
      (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
      (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
      (match Vᵥ
        [(-Vector αs)
         (for*/ans ([(α i) (in-indexed αs)]
                    #:when (exact-nonnegative-integer? i) ; hack for TR
                    #:when (plausible-index? M Γ₀ Wᵢ i)
                    [Γ* (in-value (Γ+ Γ₀ (-?@ '= sᵢ (-b i))))]
                    [V (σ@ σ α)])
           (values ⊥σ {set (-ΓW Γ* (-W (list V) sₐ))} ∅ ∅))]
        [(-Vector/hetero αs l³)
         (match-define (Mon-Info _ _ lo) l³)
         (for*/ans ([(α i) (in-indexed αs)]
                    #:when (exact-nonnegative-integer? i) ; hack for TR
                    #:when (plausible-index? M Γ₀ Wᵢ i)
                    [Γ* (in-value (Γ+ Γ₀ (-?@ '= sᵢ (-b i))))]
                    [c (in-value (and (-e? α) α))]
                    [C (σ@ σ α)])
           (define W-c (-W¹ C c))
           ((mon l³ ℓ W-c (-W¹ -●/V sₐ)) M σ (-ℒ-with-Γ ℒ₀ Γ*)))]
        [(-Vector/homo α l³)
         (match-define (Mon-Info _ _ lo) l³)
         (define c (and (-e? α) α))
         (for*/ans ([C (σ@ σ α)])
           (define W-c (-W¹ C c))
           ((mon l³ ℓ W-c (-W¹ -●/V sₐ)) M σ ℒ₀))]
        [_
         ;(printf "Warning: unsafe-vector-ref given non-vector: ~a ~n" (show-V Vᵥ))
         (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]))

    (: ap/vector-set! : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/vector-set!)
      (match-define (list Wᵥ Wᵢ Wᵤ) Wₓs)
      (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
      (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
      (match-define (-W¹ Vᵤ sᵤ) Wᵤ)
      (define Wₕᵥ (-W¹ (σ@¹ σ (-α.def havoc-𝒾)) havoc-𝒾))
      (match Vᵥ
        [(-Vector αs)
         (for*/ans ([(α i) (in-indexed αs)]
                    #:when (exact-nonnegative-integer? i) ; hack for TR
                    #:when (plausible-index? M Γ₀ Wᵢ i))
           (define Γ* (Γ+ Γ₀ (-?@ '= sᵢ (-b i))))
           (values (⊔ ⊥σ α Vᵤ) {set (-ΓW Γ* -Void/W)} ∅ ∅))]
        [(-Vector/hetero αs l³)
         (match-define (Mon-Info l+ l- lo) l³)
         (define l³* (swap-parties l³))
         (for*/ans ([(α i) (in-indexed αs)]
                    #:when (exact-nonnegative-integer? i) ; hack for TR
                    #:when (plausible-index? M Γ₀ Wᵢ i)
                    [Γ* (in-value (Γ+ Γ₀ (-?@ '= sᵢ (-b i))))]
                    [c (in-value (and (-e? α) α))]
                    [C (σ@ σ α)])
           (define W-c (-W¹ C c))
           (define ⟦chk⟧ (mon l³* ℓ W-c Wᵤ))
           (define ⟦hv⟧ ((↝.@ havoc-path ℓ (list Wₕᵥ) '()) ⟦chk⟧))
           (define comp ((↝.begin (list ⟦void⟧)) (⊔/⟦e⟧ ⟦hv⟧ ⟦void⟧)))
           (comp M σ (-ℒ-with-Γ ℒ₀ Γ*)))]
        [(-Vector/homo α l³)
         (define c (and (-e? α) α))
         (define l³* (swap-parties l³))
         (for*/ans ([C (σ@ σ α)])
           (define W-c (-W¹ C c))
           (define ⟦chk⟧ (mon l³* ℓ W-c Wᵤ))
           (define ⟦hv⟧ ((↝.@ havoc-path ℓ (list Wₕᵥ) '()) ⟦chk⟧))
           (define comp ((↝.begin (list ⟦void⟧)) (⊔/⟦e⟧ ⟦hv⟧ ⟦void⟧)))
           (comp M σ ℒ₀))]
        [_
         (define ⟦hv⟧ (ap havoc-path ℓ Wₕᵥ (list Wᵤ)))
         ((⊔/⟦e⟧ ⟦hv⟧ ⟦void⟧) M σ ℒ₀)]))

    (: ap/● : → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
    (define (ap/●)
      (define Wₕᵥ (-W¹ (σ@¹ σ (-α.def havoc-𝒾)) havoc-𝒾))
      (⊔/ans (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)
             (for*/ans ([Wₓ Wₓs])
               ((ap 'Λ ℓ Wₕᵥ (list Wₓ)) M σ ℒ₀))))

    (with-debugging/off
      ((δσ ΓWs ΓEs ℐs)
       (match Vₕ
         
         ;; Struct operators cannot be handled by `δ`, because structs can be arbitrarily wrapped
         ;; by proxies, and contract checking is arbitrarily deep
         ;; Also, there's no need to check for preconditions, because they should have been caught
         ;; by wrapping contracts
         [(-st-p s)     (ap/st-p   s  )]
         [(-st-mk s)    (ap/st-mk  s  )]
         [(-st-ac  s i) (with-guarded-arity 1 (ap/st-ac  s i))]
         [(-st-mut s i) (with-guarded-arity 2 (ap/st-mut s i))]
         ['contract-first-order-passes? (ap/contract-first-order-passes?)]
         ['vector-ref  (ap/vector-ref )]
         ['vector-set! (ap/vector-set!)]
         ['unsafe-struct-ref (ap/unsafe-struct-ref)]
         ['unsafe-struct-set! (ap/unsafe-struct-set!)]
         
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
         [(-St/C #t s αs)
          (with-guarded-arity 1
            (define cs : (Listof -s)
              (for/list ([s (-struct/c-split sₕ (-struct-info-arity s))]
                         [α αs])
                (or s (and (-e? α) α))))
            (for*/ans ([Cs (σ@/list σ αs)])
              (ap/St/C s (map -W¹ Cs cs))))]
         [(-● _)
          (case (MΓ⊢oW M Γ₀ 'procedure? Wₕ)
            [(✓ ?) (ap/●)]
            [(✗) (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅)])]
         [_ (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅)]))
      (printf "Ap: ~a ~a:~n" (show-W¹ Wₕ) (map show-W¹ Wₓs))
      (printf "answers:~n")
      (for ([A ΓWs]) (printf "  - ~a~n" (show-A A)))
      (printf "errors:~n")
      (for ([A ΓEs]) (printf "  - ~a~n" (show-A A)))
      (printf "pending:~n")
      (for ([ℐ  ℐs]) (printf "  - ~a~n" (show-ℐ ℐ)))
      (printf "~n"))))


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
    (with-debugging/off
      ((δσ ΓWs ΓEs ℐs)
       (case (MΓ⊢V∈C M Γ W-V W-C)
         [(✓) (values ⊥σ {set (-ΓW Γ (-W (list V) v))} ∅ ∅)]
         [(✗) (values ⊥σ ∅ {set (-ΓE Γ (-blm l+ lo (list C) (list V)))} ∅)]
         [(?) ((mon* l³ ℓ W-C W-V) M σ ℒ)]))
      (printf "mon ⟨~a,~a⟩ ~a ~a~n" l+ lo (show-W¹ W-C) (show-W¹ W-V))
      (printf "answers:~n")
      (for ([A ΓWs]) (printf "  - ~a~n" (show-A A)))
      (printf "errors:~n")
      (for ([A ΓEs]) (printf "  - ~a~n" (show-A A)))
      (printf "pending:~n")
      (for ([ℐ  ℐs]) (printf "  - ~a~n" (show-ℐ ℐ)))
      (printf "~n"))))

(: mon-=>_ : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-=>_ l³ ℓ W-C W-V)
  (match-define (-W¹ grd c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  
  (define arity
    (let ([a
           (match grd
             [(-=> αs _ _) (length αs)]
             [(-=>i _ β _)
              (match β
                [(-λ xs _) (formals-arity xs)]
                [_ #f])])])
      (define b (-b a))
      (-W¹ b b)))
  
  (λ (M σ ℒ)
    ;; Perform first-order checks for procedure?-ness and arity before wrapping
    (define Γ (-ℒ-cnd ℒ))
    (define-values (Γ₁ Γ₂) (Γ+/-W∋Ws M Γ -procedure?/W W-V))
    (define-values (Γ₁₁ Γ₁₂)
      (if Γ₁
          (let ([A (V-arity V)]
                [a (-?@ 'procedure-arity v)])
            (define W-a (-W¹ (if A (-b A) -●/V) a))
            (Γ+/-W∋Ws M Γ₁ -arity-includes?/W W-a arity))
          (values #f #f)))
    (define-set ΓWs : -ΓW)
    (define-set ΓEs : -ΓE)
    (define δσ : -Δσ ⊥σ)
    (when Γ₁₁
      (define grd-ℓ
        (cond [(-=>? grd) (-=>-pos grd)]
              [else (-=>i-pos grd)]))
      (define α (or (keep-if-const v) (-α.fn ℓ grd-ℓ (-ℒ-hist ℒ))))
      (define Ar (-Ar grd α l³))
      (ΓWs-add! (-ΓW Γ₁₁ (-W (list Ar) v)))
      (set! δσ (⊔ δσ α V)))
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
  (define p (-st-p s))
  (define K (let ([k (-st-mk s)]) (-W¹ k k)))
  (define muts (-struct-info-mutables s))
  
  (define ⟦field⟧s : (Listof -⟦e⟧)
    (for/list ([(α i) (in-indexed αs)])
      (define ac (-st-ac s (assert i exact-nonnegative-integer?)))
      (ap lo ℓ (-W¹ ac ac) (list (-W¹ V v)))))

  (match V ; FIXME code duplicate
    [(or (-St (== s) _) (-St* (== s) _ _ _))
     (match ⟦field⟧s
       ['()
        (λ (M σ ℒ)
          (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅))]
       [_
        (λ (M σ ℒ)
          (for*/ans ([Cs (σ@/list σ αs)])
            (match-define (cons ⟦mon-field⟧ ⟦mon-field⟧s)
              (for/list : (Listof -⟦e⟧) ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s])
                ((↝.mon.c l³ ℓ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
            (define ⟦cons⟧ ((↝.@ lo ℓ (list K) ⟦mon-field⟧s) ⟦mon-field⟧))
            (define α (-α.st (-struct-info-id s) ℓ (-ℒ-hist ℒ)))
            (define comp (if (set-empty? muts) ⟦cons⟧ ((↝.wrap.st s αs α l³) ⟦cons⟧)))
            (comp M σ ℒ)))])]
    [(or (-● _) (-St● (== s)))
     (define V● (-St● s))
     (match ⟦field⟧s
       ['()
        (λ (M σ ℒ)
          (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V●) v))} ∅ ∅))]
       [_
        (λ (M σ ℒ)
          (for*/ans ([Cs (σ@/list σ αs)])
            (define ⟦blm⟧ (blm l+ lo (list (-st-p s)) (list V)))
            (match-define (cons ⟦mon-field⟧ ⟦mon-field⟧s)
              (for/list : (Listof -⟦e⟧) ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s])
                ((↝.mon.c l³ ℓ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
            (define ⟦cons⟧ ((↝.@ lo ℓ (list K) ⟦mon-field⟧s) ⟦mon-field⟧))
            (define α (-α.st (-struct-info-id s) ℓ (-ℒ-hist ℒ)))
            (define ⟦mk⟧ (if (set-empty? muts) ⟦cons⟧ ((↝.wrap.st s αs α l³) ⟦cons⟧)))
            (define comp ((↝.if lo ⟦mk⟧ ⟦blm⟧) (ap lo ℓ (-W¹ p p) (list W-V))))
            (with-debugging/off ((δσ ΓWs ΓEs ℐs) (comp M σ ℒ))
              (printf "mon struct/c ⟨~a, ~a⟩ ~a ~a~n" l+ lo (show-W¹ W-C) (show-W¹ W-V))
              (printf "answers:~n")
              (for ([A ΓWs]) (printf "  - ~a~n" (show-A A)))
              (printf "errors:~n")
              (for ([A ΓEs]) (printf "  - ~a~n" (show-A A)))
              (printf "pending:~n")
              (for ([ℐ  ℐs]) (printf "  - ~a~n" (show-ℐ ℐ)))
              (printf "~n"))))])]
    [_ (blm l+ lo (list C) (list V))]))

(: mon-x/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-x/c l³ ℓ W-C W-V)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-x/C (and α (-α.x/c ℓ))) C)
  (define x (- ℓ)) ; FIXME hack
  (define 𝐱 (-x x))
  (λ (M σ ℒ)
    (for*/ans ([C* (σ@ σ α)])
      (define W-C* (-W¹ C* c))
      (define W-V* (-W¹ V 𝐱))
      (define bnd #|FIXME Hack|# (-binding 'values (list x) (if v (hash x v) (hash))))
      (values ⊥σ ∅ ∅ {set (-ℐ (-ℋ ℒ bnd '□) (-ℳ l³ ℓ W-C* W-V* ℒ))}))))

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
  (define (⟦ok⟧ [W-C : -W¹]) ;; HACK to make sure it's wrapped
    (mon l³ ℓ W-C W-V))
  (λ (M σ ℒ)
    (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
      (define W-C₁ (-W¹ C₁ c₁))
      (define W-C₂ (-W¹ C₂ c₂))
      (cond
        [(C-flat? C₁)
         (define ⟦chk⟧ (ap lo ℓ W-C₁ (list W-V)))
         (define ⟦mon⟧ (mon l³ ℓ W-C₂ W-V))
         (((↝.if lo (⟦ok⟧ W-C₁) ⟦mon⟧) ⟦chk⟧) M σ ℒ)]
        [(C-flat? C₂)
         (define ⟦chk⟧ (ap lo ℓ W-C₂ (list W-V)))
         (define ⟦mon⟧ (mon l³ ℓ W-C₁ W-V))
         (((↝.if lo (⟦ok⟧ W-C₂) ⟦mon⟧) ⟦chk⟧) M σ ℒ)]
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
(define (mon-vectorof l³ ℓ W_c Wᵥ)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-W¹ (-Vectorof α) _) W_c)
  (define c  (and (-e? α ) α ))
  (define ⟦rt⟧ : -⟦e⟧
    (λ (M σ ℒ)
      (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list (-Vector/homo α l³)) sᵥ))} ∅ ∅)))
  
  (match Vᵥ
    [(-Vector αs)
     (define ⟦erase⟧ : -⟦e⟧
       (let ([δσ (for/hash : -Δσ ([α αs]) (values α (set -●/V)))])
         (λ (M σ ℒ)
           (values δσ {set (-ΓW (-ℒ-cnd ℒ) -Void/W)} ∅ ∅))))
     (λ (M σ ℒ)
       (define Wₕᵥ (-W¹ (σ@¹ σ (-α.def havoc-𝒾)) havoc-𝒾))
       (for*/ans ([C (σ@ σ α)] [Vs (σ@/list σ αs)])
         (define ⟦hv⟧s : (Listof -⟦e⟧)
           (for/list ([(V* i) (in-indexed Vs)])
             (define ⟦chk⟧ (mon l³ ℓ (-W¹ C c) (-W¹ V* (-?@ 'vector-ref sᵥ (-b i)))))
             (define ⟦hv⟧ ((↝.@ lo ℓ (list Wₕᵥ) '()) ⟦chk⟧))
             (⊔/⟦e⟧ ⟦void⟧ ⟦hv⟧)))
         (define comp
           (match-let ([(cons ⟦e⟧ ⟦e⟧s) (append ⟦hv⟧s (list ⟦erase⟧ ⟦rt⟧))])
             ((↝.begin ⟦e⟧s) ⟦e⟧)))
         (comp M σ ℒ)))]
    [(-Vector/hetero αs l³*)
     (define cs : (Listof -s) (for/list ([α αs]) (and (-e? α) α)))
     (λ (M σ ℒ)
       (for*/ans ([C (σ@ σ α)] [Cs (σ@/list σ αs)])
          (define ⟦chk⟧s : (Listof -⟦e⟧)
            (for/list ([C* Cs] [c* cs] [i (in-naturals)])
              (define ⟦inner⟧ (mon l³* ℓ (-W¹ C* c*) (-W¹ -●/V (-?@ 'vector-ref sᵥ (-b i)))))
              ((↝.mon.c l³ ℓ (-W¹ C c)) ⟦inner⟧)))
          (define comp
            (match-let ([(cons ⟦e⟧ ⟦e⟧s) (append ⟦chk⟧s (list ⟦rt⟧))])
              ((↝.begin ⟦e⟧s) ⟦e⟧)))
          (comp M σ ℒ)))]
    [(-Vector/homo α* l³*)
     (define c* (and (-e? α*) α*))
     (λ (M σ ℒ)
       (for*/ans ([C* (σ@ σ α*)] [C (σ@ σ α)])
         (define ⟦inner⟧ (mon l³* ℓ (-W¹ C* c*) (-W¹ -●/V (-x #|FIXME|# -1))))
         (define ⟦chk⟧ ((↝.mon.c l³ ℓ (-W¹ C c)) ⟦inner⟧))
         (define comp ((↝.begin (list ⟦rt⟧)) ⟦chk⟧))
         (comp M σ ℒ)))]
    [(-● _)
     (define ⟦chk-vct⟧ (ap lo ℓ -vector?/W (list Wᵥ)))
     ((↝.if lo ⟦rt⟧ (blm l+ lo (list 'vector?) (list Vᵥ))) ⟦chk-vct⟧)]
    [_ (blm l+ lo (list 'vector?) (list Vᵥ))]))

(: mon-vector/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-vector/c l³ ℓ W-c Wᵥ)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ Vᵥ vᵥ) Wᵥ)
  (match-define (-W¹ C  c ) W-c)
  (match-define (-Vector/C αs) C)
  (define n (length αs))
  (define N (let ([b (-b n)]) (-W¹ b b)))
  (define cs
    (let ([ss (-app-split c 'vector/c n)])
      (for/list : (Listof -s) ([s ss] [α αs])
        (or s (and (-e? α) α)))))
  (define ⟦chk-vct⟧ (ap lo ℓ -vector?/W (list Wᵥ)))
  (define ⟦chk-len⟧
    (let ([⟦len⟧ (ap lo ℓ -vector-length/W (list Wᵥ))])
      ((↝.@ lo ℓ (list N -=/W) '()) ⟦len⟧)))
  (define ⟦blm-vct⟧ (blm l+ lo (list 'vector?) (list Vᵥ)))
  (define ⟦blm-len⟧ (blm l+ lo (list (format-symbol "length ~a" n)) (list Vᵥ)))
  (define ⟦mk⟧ : -⟦e⟧
    (let ([V* (-Vector/hetero αs l³)])
      (λ (M σ ℒ)
        (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V*) vᵥ))} ∅ ∅))))

  (λ (M σ ℒ)
    (define Wₕᵥ (-W¹ (σ@¹ σ (-α.def havoc-𝒾)) havoc-𝒾))
    (for*/ans ([Cs (σ@/list σ αs)])
      (define ⟦hv-fld⟧s : (Listof -⟦e⟧)
        (for/list ([C* Cs] [c* cs] [i (in-naturals)])
          (define W-c* (-W¹ C* c*))
          (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
          (define ⟦ref⟧ (ap lo ℓ -vector-ref/W (list Wᵥ Wᵢ)))
          (define ⟦mon⟧ ((↝.mon.c l³ ℓ W-c*) ⟦ref⟧))
          (define ⟦hv⟧ ((↝.@ 'Λ ℓ (list Wₕᵥ) '()) ⟦mon⟧))
          (⊔/⟦e⟧ ⟦void⟧ ⟦hv⟧)))
      (define ⟦erase⟧ : -⟦e⟧
        (match Vᵥ
          [(-Vector αs)
           (define δσ (for/hash : -Δσ ([α αs]) (values α {set -●/V})))
           (λ (M σ ℒ)
             (values δσ {set (-ΓW (-ℒ-cnd ℒ) -Void/W)} ∅ ∅))]
          [_ ⟦void⟧]))
      (define ⟦wrp⟧
        (match-let ([(cons ⟦e⟧ ⟦e⟧s) (append ⟦hv-fld⟧s (list ⟦erase⟧ ⟦mk⟧))])
          ((↝.begin ⟦e⟧s) ⟦e⟧)))
      (define comp ((↝.if lo ((↝.if lo ⟦wrp⟧ ⟦blm-len⟧) ⟦chk-len⟧) ⟦blm-vct⟧) ⟦chk-vct⟧))
      (comp M σ ℒ))))

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
        (with-debugging/off
          ((δσ ΓWs ΓEs ℐs)
           (with-guarded-arity 1 (lo Γ* Vs)
             (match-define (list V) Vs)
             (define W-V (-W¹ V v))
             ;; If contract is evaluated, check with it, otherwise evaluate it before checking
             (define ⟦mon⟧
               (cond [(-W¹? Ctc) (   mon   l³ ℓ Ctc  W-V)]
                     [else       ((↝.mon.v l³ ℓ W-V) Ctc)]))
             (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))))
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
             (for/fold ([ρ* : -ρ ρ] [δσ : -Δσ ⊥σ] [Γ* : -Γ Γ*])
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
           (define-values (δσ* ΓWs ΓEs ℐs) (⟦e⟧ M σ₁ (-ℒ-with-Γ ℒ* Γ₁)))
           
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
                [(-ℐ (-ℋ ℒ bnd ℰ) τ)
                 (define Γ* (Γ↓ (-ℒ-cnd ℒ) xs₀))
                 (define bnd* (bnd↓ bnd xs₀))
                 (-ℐ (-ℋ (-ℒ-with-Γ ℒ Γ*) bnd* ℰ) τ)])
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
