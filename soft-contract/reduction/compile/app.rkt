#lang typed/racket/base

(provide app mon flat-chk
         ap∷ let∷ if∷ and∷ or∷ bgn∷ bgn0.v∷ bgn0.e∷ rst-Γ∷
         mon.c∷ mon.v∷
         make-memoized-⟦k⟧
         mk-mon-⟦e⟧ mk-rt-⟦e⟧ mk-app-⟦e⟧
         add-leak!)

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "../../primitives/main.rkt"
         "../../externals/def-ext-runtime.rkt"
         "utils.rkt"
         "base.rkt"
         racket/set
         racket/match
         (only-in racket/list split-at))

(: app : -$ -ℒ -W¹ (Listof -W¹) -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (app $ ℒ Wₕ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ σₖ M) Σ)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define l (ℓ-src (-ℒ-app ℒ)))

  (: blm-arity ([Arity Natural] [#:name -s] . ->* . -blm))
  (define (blm-arity required provided #:name [f sₕ])
    ;; HACK for error message. Probably no need to fix
    (define msg : Symbol
      (cond
        [f (format-symbol "~a requires ~a arguments" (format "~a" (show-e f)) required)]
        [else (format-symbol "require ~a arguments" required)]))
    (-blm l 'Λ (list msg) (map -W¹-V Wₓs) (-ℒ-app ℒ)))

  (define-syntax-rule (with-guarded-arity a* e ...)
    (let ([n (length Wₓs)]
          [a a*])
      (cond
        [(arity-includes? a n) e ...]
        [else (⟦k⟧ (blm-arity a n) $ Γ ⟪ℋ⟫ Σ)])))

  (define (app-And/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
    (define ⟦rhs⟧ (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W₂) (list (mk-rt-⟦e⟧ (car Wₓs)))))
    (app $ ℒ W₁ Wₓs Γ ⟪ℋ⟫ Σ (and∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))

  (define (app-Or/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
    (define ⟦rhs⟧ (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W₂) (list (mk-rt-⟦e⟧ (car Wₓs)))))
    (app $ ℒ W₁ Wₓs Γ ⟪ℋ⟫ Σ (or∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))
  
  (define (app-Not/C [Wᵤ : -W¹]) : (℘ -ς)
    (app $ ℒ Wᵤ Wₓs Γ ⟪ℋ⟫ Σ (neg∷ l ⟦k⟧)))

  (define (app-St/C [𝒾 : -𝒾] [W-Cs : (Listof -W¹)]) : (℘ -ς)
    ;; TODO fix ℓ
    (match-define (list Wₓ) Wₓs)
    (match-define (-W¹ Vₓ _) Wₓ)
    (match Vₓ
      [(or (-St (== 𝒾) _) (-St* (-St/C _ (== 𝒾) _) _ _))
       (define ⟦chk-field⟧s : (Listof -⟦e⟧)
         (for/list ([W-C (in-list W-Cs)]
                    [i (in-naturals)] #:when (index? i))
           (define Ac (let ([ac (-st-ac 𝒾 i)]) (-W¹ ac ac)))
           (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W-C)
                       (list (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ Ac) (list (mk-rt-⟦e⟧ Wₓ)))))))
       (define P (let ([p (-st-p 𝒾)]) (-W¹ p p)))
       (app $ ℒ P (list Wₓ) Γ ⟪ℋ⟫ Σ (and∷ l ⟦chk-field⟧s ⊥ρ ⟦k⟧))]
      [_
       (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)]))

  (match Vₕ
    ;; In the presence of struct contracts, field accessing is not an atomic operation
    ;; because structs can be contract-wrapped arbitrarily deeply,
    ;; plus contracts can be arbitrary code.
    ;; This means field accessing cannot be implemented in `δ`
    [(-st-p  𝒾) ((app-st-p 𝒾) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-st-mk 𝒾) ((app-st-mk 𝒾) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-st-ac  𝒾 i) ((app-st-ac  𝒾 i) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-st-mut 𝒾 i) ((app-st-mut 𝒾 i) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    ['apply (app-apply $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    ['make-sequence (app-make-sequence $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]

    ;; Regular stuff
    [(? symbol? o) ((app-prim-or-ext o) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-Clo xs ⟦e⟧ ρₕ Γₕ)
     (with-guarded-arity (formals-arity xs)
       ((app-clo xs ⟦e⟧ ρₕ Γₕ sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧))]
    [(-Case-Clo clauses ρₕ Γₕ)
     ((app-Case-Clo clauses ρₕ Γₕ sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-Ar C α l³)
     (with-guarded-arity (guard-arity C)
       (define-values (c _) (-ar-split sₕ))
       (cond
         [(-=>? C)
          (for/union : (℘ -ς) ([Vᵤ (σ@ σ α)] #:unless (equal? Vₕ Vᵤ))
             ((app-Ar C c Vᵤ sₕ l³) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧))]
         [(-=>i? C)
          (for/union : (℘ -ς) ([Vᵤ (σ@ σ α)] #:unless (equal? Vₕ Vᵤ))
             ((app-Indy C c Vᵤ sₕ l³) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧))]
         [else
          (for/union : (℘ -ς) ([Vᵤ (σ@ σ α)] #:unless (equal? Vₕ Vᵤ))
             ((app-guarded-Case C c Vᵤ sₕ l³) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧))]))]
    [(-And/C #t (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (with-guarded-arity 1
       (define-values (c₁ c₂)
         (match-let ([(list s₁ s₂) (-app-split sₕ 'and/c 2)])
           (values (or s₁ (⟪α⟫->s α₁))
                   (or s₂ (⟪α⟫->s α₂)))))
       (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
         (app-And/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
    [(-Or/C #t (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (with-guarded-arity 1
       (define-values (c₁ c₂)
         (match-let ([(list s₁ s₂) (-app-split sₕ 'or/c 2)])
           (values (or s₁ (⟪α⟫->s α₁))
                   (or s₂ (⟪α⟫->s α₂)))))
       (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
         (app-Or/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
    [(-Not/C (cons α ℓ*))
     (with-guarded-arity 1
       (define c*
         (match-let ([(list s) (-app-split sₕ 'not/c 1)])
           (or s (⟪α⟫->s α))))
       (for/union : (℘ -ς) ([C* (σ@ σ α)])
         (app-Not/C (-W¹ C* c*))))]
    [(-St/C #t s αℓs)
     (with-guarded-arity 1
       (define-values (αs ℓs) ((inst unzip ⟪α⟫ ℓ) αℓs))
       (define cs : (Listof -s)
         (for/list ([s (-struct/c-split sₕ s)]
                    [α : ⟪α⟫ αs])
           (or s (⟪α⟫->s α))))
       (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
         (app-St/C s (map -W¹ Cs cs))))]
    [(-● _)
     (case (MΓ⊢oW M σ Γ 'procedure? Wₕ)
       [(✓ ?) ((app-opq sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
       [(✗) (⟦k⟧ (-blm l 'Λ (list 'procedure?) (list Vₕ) (-ℒ-app ℒ)) $ Γ ⟪ℋ⟫ Σ)])]
    [_
     (define blm (-blm l 'Λ (list 'procedure?) (list Vₕ) (-ℒ-app ℒ)))
     (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))

(: add-leak! : -Σ -V → Void)
(define (add-leak! Σ V)
  (when (behavioral? (-Σ-σ Σ) V)
    (σ⊕! Σ ⟪α⟫ₕᵥ V)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Applications
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: app-prim-or-ext : Symbol → -⟦f⟧)
(define ((app-prim-or-ext o) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (cond
    [(get-prim o) =>
     (λ ([⟦o⟧ : -⟦o⟧])
       (match-define (-ℒ _ ℓ) ℒ)
       (for/union : (℘ -ς) ([ΓA (in-set (⟦o⟧ ⟪ℋ⟫ ℓ Σ Γ Wₓs))])
          (match-define (-ΓA Γ A) ΓA)
          (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))]
    [(get-ext o) =>
     (λ ([⟦f⟧ : -⟦f⟧])
       (⟦f⟧ $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧))]
    [else (error 'app "don't know how to apply `~a`" o)]))

(: app-clo : -formals -⟦e⟧ -ρ -Γ -s → -⟦f⟧)
(define ((app-clo xs ⟦e⟧ ρₕ Γₕ sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))

  (define plausible? ; conserivative `plausible?` to filter out some
    (cond [sₕ
           (for/and : Boolean ([γ (in-list (-Γ-tails Γ))])
             (match-define (-γ αₖ _ sₕ* _) γ)
             (cond [(equal? sₕ sₕ*)
                    (and (-ℬ? αₖ) (equal? (-ℬ-exp αₖ) ⟦e⟧))]
                   [else #t]))]
          [else #t]))

  (cond
    [plausible?
     (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ (-edge ⟦e⟧ ℒ)))
     ;; Target's environment
     (define ρ* : -ρ
       (match xs
         [(? list? xs)
          (alloc-init-args! Σ Γ ρₕ ⟪ℋ⟫ₑₑ xs Wₓs)]
         [(-var zs z)
          (define-values (Ws₀ Wsᵣ) (split-at Wₓs (length zs)))
          (define ρ₀ (alloc-init-args! Σ Γ ρₕ ⟪ℋ⟫ₑₑ zs Ws₀))
          (define Vᵣ (alloc-rest-args! Σ Γ ⟪ℋ⟫ₑₑ ℒ Wsᵣ))
          (define αᵣ (-α->⟪α⟫ (-α.x z ⟪ℋ⟫ₑₑ)))
          (σ⊕! Σ αᵣ Vᵣ)
          (ρ+ ρ₀ z αᵣ)]))

     (define αₖ (-ℬ xs ⟦e⟧ ρ*))
     (define κ (-κ (make-memoized-⟦k⟧ ⟦k⟧) Γ ⟪ℋ⟫ sₕ sₓs))
     (σₖ⊔! Σ αₖ κ)
     {set (-ς↑ αₖ Γₕ ⟪ℋ⟫ₑₑ)}]
    [else ∅]))

(: apply-app-clo : (-var Symbol) -⟦e⟧ -ρ -Γ -s
   → -$ -ℒ (Listof -W¹) -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define ((apply-app-clo xs ⟦e⟧ ρₕ Γₕ sₕ) $ ℒ Ws₀ Wᵣ Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-var xs₀ xᵣ) xs)
  (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ (-edge ⟦e⟧ ℒ)))
  (match-define (-W¹ Vᵣ sᵣ) Wᵣ)
  (define ρ*
    (let ([ρ₀ (alloc-init-args! Σ Γ ρₕ ⟪ℋ⟫ₑₑ xs₀ Ws₀)])
      (define αᵣ (-α->⟪α⟫ (-α.x xᵣ ⟪ℋ⟫ₑₑ)))
      (σ⊕! Σ αᵣ Vᵣ)
      (ρ+ ρ₀ xᵣ αᵣ)))
  (define αₖ (-ℬ xs ⟦e⟧ ρ*))
  (define κ
    (let ([ss₀ (map -W¹-s Ws₀)]
          [sᵣ (-W¹-s Wᵣ)])
      (-κ (make-memoized-⟦k⟧ ⟦k⟧) Γ ⟪ℋ⟫ 'apply `(,sₕ ,@ss₀ ,sᵣ))))
  (σₖ⊔! Σ αₖ κ)
  {set (-ς↑ αₖ Γₕ ⟪ℋ⟫ₑₑ)})

(: app-Case-Clo : (Listof (Pairof (Listof Symbol) -⟦e⟧)) -ρ -Γ -s → -⟦f⟧)
(define ((app-Case-Clo clauses ρₕ Γₕ sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (define n (length Wₓs))
  (define clause
    (for/or : (Option (Pairof (Listof Symbol) -⟦e⟧)) ([clause clauses])
      (match-define (cons xs _) clause)
      (and (equal? n (length xs)) clause)))
  (cond
    [clause
     (match-define (cons xs ⟦e⟧) clause)
     ((app-clo xs ⟦e⟧ ρₕ Γₕ sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [else
     (define a : (Listof Index) (for/list ([clause clauses]) (length (car clause))))
     (define-values (ℓ l) (unpack-ℒ ℒ))
     (define blm (-blm l 'Λ (list (format-symbol "arity among ~a" a)) (map -W¹-V Wₓs) ℓ))
     (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))

(: app-guarded-Case : -V -s -V -s -l³ → -⟦f⟧)
(define ((app-guarded-Case C c Vᵤ sₕ l³) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (error 'app-guarded-Case "TODO"))

(: app-Ar : -=> -s -V -s -l³ → -⟦f⟧)
(define ((app-Ar C c Vᵤ sₕ l³) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-l³ l+ l- lo) l³)
  (define Wᵤ (-W¹ Vᵤ sₕ)) ; inner function
  (match-define (-=> αℓs βℓ _) C)
  (match-define (cons β ℓₐ) βℓ)
  (define-values (cs d) (-->-split c (shape αℓs)))
  (match-define (-Σ σ _ _) Σ)
  (define l³* (-l³ l- l+ lo))
  (match* (αℓs cs)
    [('() '()) ; no arg
     (for/union : (℘ -ς) ([D (σ@ σ β)])
                (app $ ℒ Wᵤ '() Γ ⟪ℋ⟫ Σ
                     (mon.c∷ l³ (ℒ-with-mon ℒ ℓₐ) (-W¹ D d) ⟦k⟧)))]
    [((? pair?) (? pair?))
     (define-values (αs ℓs) ((inst unzip ⟪α⟫ ℓ) αℓs))
     (for*/union : (℘ -ς) ([Cs (in-set (σ@/list σ αs))]
                           [D (in-set (σ@ σ β))])
        (match-define (cons ⟦mon-x⟧ ⟦mon-x⟧s)
          (for/list : (Listof -⟦e⟧) ([C Cs]
                                     [c cs]
                                     [Wₓ Wₓs]
                                     [ℓₓ : ℓ ℓs])
            (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₓ) (mk-rt-⟦e⟧ (-W¹ C c)) (mk-rt-⟦e⟧ Wₓ))))
        (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
         (ap∷ (list Wᵤ) ⟦mon-x⟧s ⊥ρ lo ℒ
              (mon.c∷ l³ (ℒ-with-mon ℒ ℓₐ) (-W¹ D d) ⟦k⟧))))]
    [((-var αℓs₀ αℓᵣ) (-var cs₀ cᵣ))
     (define-values (αs₀ ℓs₀) ((inst unzip ⟪α⟫ ℓ) αℓs₀))
     (match-define (cons αᵣ ℓᵣ) αℓᵣ)
     (define-values (Ws₀ Wsᵣ) (split-at Wₓs (length αs₀)))
     (define Vᵣ (alloc-rest-args! Σ Γ ⟪ℋ⟫ (ℒ-with-mon ℒ ℓᵣ) Wsᵣ))
     (define Wᵣ (-W¹ Vᵣ (-?list (map -W¹-s Wsᵣ))))
     (for*/union : (℘ -ς) ([Cs₀ (in-set (σ@/list σ αs₀))]
                           [Cᵣ (in-set (σ@ σ αᵣ))]
                           [D (in-set (σ@ σ β))])
       (define ⟦mon-x⟧s : (Listof -⟦e⟧)
         (for/list ([Cₓ Cs₀] [cₓ cs₀] [Wₓ Ws₀] [ℓₓ : ℓ ℓs₀])
           (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₓ) (mk-rt-⟦e⟧ (-W¹ Cₓ cₓ)) (mk-rt-⟦e⟧ Wₓ))))
       (define ⟦mon-x⟧ᵣ : -⟦e⟧
         (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓᵣ) (mk-rt-⟦e⟧ (-W¹ Cᵣ cᵣ)) (mk-rt-⟦e⟧ Wᵣ)))
       (match ⟦mon-x⟧s
         ['()
          (⟦mon-x⟧ᵣ ⊥ρ $ Γ ⟪ℋ⟫ Σ
           (ap∷ (list Wᵤ -apply/W) '() ⊥ρ lo ℒ
                (mon.c∷ l³ (ℒ-with-mon ℒ ℓₐ) (-W¹ D d) ⟦k⟧)))]
         [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
          (⟦mon-x⟧₀ ⊥ρ $ Γ ⟪ℋ⟫ Σ
           (ap∷ (list Wᵤ -apply/W) `(,@ ⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ lo ℒ
                (mon.c∷ l³ (ℒ-with-mon ℒ ℓₐ) (-W¹ D d) ⟦k⟧)))]))]))

(: apply-app-Ar : -=> -s -V -s -l³
   → -$ -ℒ (Listof -W¹) -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define ((apply-app-Ar C c Vᵤ sₕ l³) $ ℒ Ws₀ Wᵣ Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-=> (-var αℓs₀ (cons αᵣ ℓᵣ)) (cons β ℓₐ) _) C)
  (match-define-values ((-var cs₀ cᵣ) d) (-->-split c (arity-at-least (length αℓs₀))))
  ;; FIXME copied n pasted from app-Ar
  (define-values (αs₀ ℓs₀) ((inst unzip ⟪α⟫ ℓ) αℓs₀))
  (match-define (-W¹ Vᵣ sᵣ) Wᵣ)
  (match-define (-l³ l+ l- lo) l³)
  (define l³* (-l³ l- l+ lo))
  (define Wᵤ (-W¹ Vᵤ sₕ))
  (for*/union : (℘ -ς) ([Cs₀ (in-set (σ@/list Σ αs₀))]
                        [Cᵣ (in-set (σ@ Σ αᵣ))]
                        [D (in-set (σ@ Σ β))])
    (define ⟦mon-x⟧s : (Listof -⟦e⟧)
      (for/list ([Cₓ Cs₀] [cₓ cs₀] [Wₓ Ws₀] [ℓₓ : ℓ ℓs₀])
        (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₓ) (mk-rt-⟦e⟧ (-W¹ Cₓ cₓ)) (mk-rt-⟦e⟧ Wₓ))))
    (define ⟦mon-x⟧ᵣ : -⟦e⟧
      (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓᵣ) (mk-rt-⟦e⟧ (-W¹ Cᵣ cᵣ)) (mk-rt-⟦e⟧ Wᵣ)))
    (match ⟦mon-x⟧s
      ['()
       (⟦mon-x⟧ᵣ ⊥ρ $ Γ ⟪ℋ⟫ Σ
        (ap∷ (list Wᵤ -apply/W) '() ⊥ρ lo ℒ
             (mon.c∷ l³ (ℒ-with-mon ℒ ℓₐ) (-W¹ D d) ⟦k⟧)))]
      [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
       (⟦mon-x⟧₀ ⊥ρ $ Γ ⟪ℋ⟫ Σ
        (ap∷ (list Wᵤ -apply/W) `(,@ ⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ lo ℒ
             (mon.c∷ l³ (ℒ-with-mon ℒ ℓₐ) (-W¹ D d) ⟦k⟧)))])))

(: app-Indy : -=>i -s -V -s -l³ → -⟦f⟧)
(define ((app-Indy C c Vᵤ sₕ l³) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-l³ l+ l- lo) l³)
  (define l³* (-l³ l- l+ lo))
  (define Wᵤ (-W¹ Vᵤ sₕ)) ; inner function
  (match-define (-=>i αℓs (list Mk-D mk-d ℓᵣ) _) C)
  (match-define (-Clo xs ⟦d⟧ ρᵣ _) Mk-D)
  (define W-rng (-W¹ Mk-D mk-d))
  (define-values (αs ℓs) ((inst unzip ⟪α⟫ ℓ) αℓs))
  (define cs
    (let-values ([(cs _) (-->i-split c (length αℓs))])
      cs))

  ;; FIXME tmp. copy n paste. Remove duplication
  (match mk-d
    [(-λ (? list? xs) d)
     (for/union : (℘ -ς) ([Cs (σ@/list Σ αs)])
       (define ⟦mon-x⟧s : (Listof -⟦e⟧)
         (for/list ([C Cs] [c cs] [Wₓ Wₓs] [ℓₐ : ℓ ℓs])
           (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₐ) (mk-rt-⟦e⟧ (-W¹ C c)) (mk-rt-⟦e⟧ Wₓ))))
       (define ⟦x⟧s : (Listof -⟦e⟧) (for/list ([x xs]) (↓ₓ 'Λ x)))
       (match* (xs ⟦x⟧s ⟦mon-x⟧s)
         [('() '() '())
          (define ⟦ap⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ) '()))
          (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦d⟧ ⟦ap⟧))
          (⟦mon⟧ ρᵣ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
         [((cons x xs*) (cons ⟦x⟧ ⟦x⟧s*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
          (define ⟦app⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ) ⟦x⟧s))
          (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦d⟧ ⟦app⟧))
          (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
           (let∷ (-ℒ-app ℒ)
                 (list x)
                 (for/list ([xᵢ xs*] [⟦mon⟧ᵢ ⟦mon-x⟧s*])
                   (cons (list xᵢ) ⟦mon⟧ᵢ))
                 '()
                 ⟦mon⟧
                 ρᵣ
                 ⟦k⟧))]))]
    [_
     (match xs
       [(? list? xs)
        (define ⟦x⟧s : (Listof -⟦e⟧) (for/list ([x xs]) (↓ₓ lo x)))
        (for/union : (℘ -ς) ([Cs (σ@/list Σ αs)] [ℓₐ : ℓ ℓs])
           (define ⟦mon-x⟧s : (Listof -⟦e⟧)
             (for/list ([C Cs] [c cs] [Wₓ Wₓs])
               (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₐ) (mk-rt-⟦e⟧ (-W¹ C c)) (mk-rt-⟦e⟧ Wₓ))))
           (match* (xs ⟦x⟧s ⟦mon-x⟧s)
             [('() '() '())
              (define ⟦app⟧  (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ   ) '()))
              (define ⟦mk-d⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ W-rng) '()))
              (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦mk-d⟧ ⟦app⟧))
              (⟦mon⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
             [((cons x xs*) (cons ⟦x⟧ ⟦x⟧s*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
              (define ⟦mon-y⟧
                (let ([⟦mk-d⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ W-rng) ⟦x⟧s)]
                      [⟦app⟧  (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ   ) ⟦x⟧s)])
                  (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦mk-d⟧ ⟦app⟧)))
              (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
               (let∷ (-ℒ-app ℒ)
                     (list x)
                     (for/list ([xᵢ xs*] [⟦mon⟧ᵢ ⟦mon-x⟧s*])
                       (cons (list xᵢ) ⟦mon⟧ᵢ))
                     '()
                     ⟦mon-y⟧
                     ⊥ρ
                      ⟦k⟧))]))]
       [(-var zs z)
        (error 'app-Indy "Apply variable arity arrow")])]))

(: app-st-p : -𝒾 → -⟦f⟧)
(define (app-st-p 𝒾)
  (define st-p (-st-p 𝒾))
  (λ ($ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match Ws
      [(list (and W (-W¹ _ s)))
       (match-define (-Σ σ _ M) Σ)
       (define sₐ (-?@ st-p s))
       (define A
         (case (MΓ⊢oW M σ Γ st-p W)
           [(✓) -True/Vs]
           [(✗) -False/Vs]
           [(?) -Bool/Vs]))
       (⟦k⟧ (-W A sₐ) $ Γ ⟪ℋ⟫ Σ)]
      [_
       (define blm (blm-arity (-ℒ-app ℒ) (show-o st-p) 1 (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(: app-st-mk : -𝒾 → -⟦f⟧)
(define (app-st-mk 𝒾)
  (define st-mk (-st-mk 𝒾))
  (define n (get-struct-arity 𝒾))
  (λ ($ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (cond
      [(= n (length Ws))
       (match-define (-Σ σ _ M) Σ)
       (define sₐ (apply -?@ st-mk (map -W¹-s Ws)))
       (define αs : (Listof ⟪α⟫)
         (for/list ([i : Index n])
           (-α->⟪α⟫ (-α.fld 𝒾 ℒ ⟪ℋ⟫ i))))
       (for ([α : ⟪α⟫ αs] [W (in-list Ws)])
         (match-define (-W¹ V s) W)
         (define V* (V+ σ V (predicates-of Γ s)))
         (σ⊕! Σ α V*))
       (define V (-St 𝒾 αs))
       (⟦k⟧ (-W (list V) sₐ) $ Γ ⟪ℋ⟫ Σ)]
      [else
       (define blm (blm-arity (-ℒ-app ℒ) (show-o st-mk) n (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(: app-st-ac : -𝒾 Index → -⟦f⟧)
(define (app-st-ac 𝒾 i)
  (define ac (-st-ac 𝒾 i))
  (define p  (-st-p 𝒾))
  (define n (get-struct-arity 𝒾))
  
  (: ⟦ac⟧ : -⟦f⟧)
  (define (⟦ac⟧ $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match Ws
      [(list (and W (-W¹ V s)))
       (define-values (ℓ l) (unpack-ℒ ℒ))
       (define (blm) (-blm l (show-o ac) (list p) (list V) ℓ))
       (match-define (-Σ σ _ M) Σ)
       (match V
         [(-St (== 𝒾) αs)
          (define α (list-ref αs i))
          (define old? (σ-old? σ α))
          (define sₐ (and old? (-?@ ac s)))
          (cond
            [(and old? ($@ $ sₐ)) =>
             (λ ([V : -V])
               (cond [(plausible-V-s? (-Γ-facts Γ) V sₐ)
                      (define $* ($+ $ sₐ V))
                      (⟦k⟧ (-W (list V) sₐ) $* Γ ⟪ℋ⟫ Σ)]
                     [else ∅]))]
            [else
             (define Vs (σ@ σ α))
             (for/union : (℘ -ς) ([V Vs])
                (cond [(plausible-V-s? (-Γ-facts Γ) V sₐ)
                       (define $* ($+ $ sₐ V))
                       (⟦k⟧ (-W (list V) sₐ) $* Γ ⟪ℋ⟫ Σ)]
                      [else ∅]))])]
         [(-St* (-St/C _ (== 𝒾) αℓs) α l³)
          (match-define (-l³ _ _ lₒ) l³)
          (define Ac (-W¹ ac ac))
          (cond
            ;; mutable field should be wrapped
            [(struct-mutable? 𝒾 i)
             (match-define (cons αᵢ ℓᵢ) (list-ref αℓs i))
             (define Cᵢs (σ@ σ αᵢ))
             (define Vs  (σ@ σ α))
             (define cᵢ (⟪α⟫->s αᵢ))
             (for*/union : (℘ -ς) ([Cᵢ (in-set Cᵢs)] [V* (in-set Vs)])
               (⟦ac⟧ $ ℒ (list (-W¹ V* s)) Γ ⟪ℋ⟫ Σ
                (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵢ) (-W¹ Cᵢ cᵢ) ⟦k⟧)))]
            ;; no need to check immutable field
            [else
             ;; TODO: could this loop forever due to cycle?
             (for/union : (℘ -ς) ([V* (in-set (σ@ σ α))])
                (⟦ac⟧ $ ℒ (list (-W¹ V* s)) Γ ⟪ℋ⟫ Σ ⟦k⟧))])]
         [(-● ps)
          (with-Γ+/- ([(Γₒₖ Γₑᵣ) (MΓ+/-oW M σ Γ p W)])
            #:true  (⟦k⟧ (-W (if (and (equal? 𝒾 -𝒾-cons) (equal? i 1) (∋ ps 'list?))
                                 (list (-● {set 'list?}))
                                 -●/Vs)
                             (-?@ ac s))
                     $ Γₒₖ ⟪ℋ⟫ Σ)
            #:false (⟦k⟧ (blm) $ Γₑᵣ ⟪ℋ⟫ Σ))]
         [_ (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)])]
      [_
       (define blm (blm-arity (-ℒ-app ℒ) (show-o ac) 1 (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
  ⟦ac⟧)

(: app-st-mut : -𝒾 Index → -⟦f⟧)
(define (app-st-mut 𝒾 i)
  (define mut (-st-mut 𝒾 i))
  (define p (-st-p 𝒾))
  
  (: ⟦mut⟧ : -⟦f⟧)
  (define (⟦mut⟧ $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match Ws
      [(list Wₛ Wᵥ)
       (match-define (-Σ σ _ M) Σ)
       (match-define (-W¹ Vₛ sₛ) Wₛ)
       (match-define (-W¹ Vᵥ _ ) Wᵥ)
       (define-values (ℓ l) (unpack-ℒ ℒ))
       (define (blm)
         (-blm l (show-o mut) (list p) (list Vₛ) ℓ))
       
       (match Vₛ
         [(-St (== 𝒾) αs)
          (define α (list-ref αs i))
          (σ⊕! Σ α Vᵥ #:mutating? #t)
          (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)]
         [(-St* (-St/C _ (== 𝒾) γℓs) α l³)
          (match-define (-l³ l+ l- lo) l³)
          (define l³* (-l³ l- l+ lo))
          (match-define (cons γ ℓᵢ) (list-ref γℓs i))
          (define c (⟪α⟫->s γ))
          (define Mut (-W¹ mut mut))
          (for*/union : (℘ -ς) ([C (σ@ σ γ)] [Vₛ* (σ@ σ α)])
                      (define W-c (-W¹ C c))
                      (define Wₛ* (-W¹ Vₛ* sₛ))
                      (mon l³* $ (ℒ-with-mon ℒ ℓᵢ) W-c Wᵥ Γ ⟪ℋ⟫ Σ
                           (ap∷ (list Wₛ* Mut) '() ⊥ρ lo ℒ ⟦k⟧)))]
         [(-● _)
          (define ⟦ok⟧
            (let ([⟦hv⟧ (mk-app-⟦e⟧ 'havoc ℒ
                                    (mk-rt-⟦e⟧ (-W¹ -●/V #f))
                                    (list (mk-rt-⟦e⟧ Wᵥ)))])
              (mk-app-⟦e⟧ 'havoc ℒ (mk-rt-⟦e⟧ (-W¹ 'void 'void)) (list ⟦hv⟧))))
          (define ⟦er⟧ (mk-rt-⟦e⟧ (blm)))
          (app $ ℒ (-W¹ p p) (list Wₛ) Γ ⟪ℋ⟫ Σ (if∷ l ⟦ok⟧ ⟦er⟧ ⊥ρ ⟦k⟧))]
         [_ (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)])]
      [_
       (define blm (blm-arity (-ℒ-app ℒ) (show-o mut) 2 (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
  ⟦mut⟧)

(: app-apply : -⟦f⟧)
(define (app-apply $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME
  (match-define (-Σ σ _ M) Σ)
  (match Ws
    [(cons Wₕ Wₓs)
     (match-define (-W¹ Vₕ sₕ) Wₕ)
     
     (: blm : -V → -Γ → (℘ -ς))
     (define ((blm C) Γ)
       (define-values (ℓ l) (unpack-ℒ ℒ))
       (define blm (-blm l 'apply (list C) (list Vₕ) ℓ))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

     (: do-apply : -Γ → (℘ -ς))
     (define (do-apply Γ)
       (define num-init-args (sub1 (length Wₓs)))
       (match-define-values (Ws₀ (list Wᵣ)) (split-at Wₓs num-init-args))
       
       (match Vₕ
         [(-Clo xs ⟦e⟧ ρₕ Γₕ)
          (match (formals-arity xs)
            [(arity-at-least (== num-init-args))
             ((apply-app-clo (assert xs -var?) ⟦e⟧ ρₕ Γₕ sₕ) $ ℒ Ws₀ Wᵣ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
            [_ (error 'do-apply "~a~n" (show-V Vₕ))])]
         [(-Case-Clo clauses _ _)
          (error 'do-apply "TODO: case->: ~a" (show-V Vₕ))]
         [(-Ar C ⟪α⟫ᵥ l³)
          (cond
            [(-=>? C)
             (match (guard-arity C)
               [(arity-at-least (== num-init-args))
                (define-values (c _) (-ar-split sₕ))
                (for/union : (℘ -ς) ([Vᵤ (in-set (σ@ Σ ⟪α⟫ᵥ))] #:unless (equal? Vᵤ Vₕ))
                   ((apply-app-Ar C c Vᵤ sₕ l³) $ ℒ Ws₀ Wᵣ Γ ⟪ℋ⟫ Σ ⟦k⟧))]
               [a
                (error 'do-apply "TODO: guarded function ~a with arity ~a" (show-V Vₕ) a)])]
            [else
             (error 'do-apply "TODO: guarded function ~a" (show-V Vₕ))])]
         [(? -o? o)
          (error 'do-apply "TODO: primmitive: ~a" (show-V Vₕ))]
         [(-● _)
          ((app-opq sₕ) $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
         [_
          (printf "Warning: unhandled in `app-apply`: ~a~n" (show-V Vₕ))
          ∅]))
     
     (with-MΓ⊢oW (M σ Γ 'procedure? Wₕ)
       #:on-t do-apply
       #:on-f (blm 'procedure?))]
    [_
     (define-values (ℓ l) (unpack-ℒ ℒ))
     (define blm (blm-arity ℓ l (arity-at-least 2) (map -W¹-V Ws)))
     (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])
  
  
  #;(match* (W₀ Wᵢs)
    [((-W¹ (-Clo (-var (list x) xᵣ) ⟦e⟧ ρ Γ) sₕ) (list W₁ W₂ Wᵣ))
     (match-define (-W¹ V₂ s₂) W₂)
     (match-define (-W¹ Vᵣ sᵣ) Wᵣ)
     (define Wₗ
       (let ([sₗ (-?@ -cons s₂ sᵣ)]
             [αₕ (-α->⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ 0))]
             [αₜ (-α->⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ 1))])
         (define Vₗ (-Cons αₕ αₜ))
         (σ⊕*! Σ [αₕ ↦ V₂] [αₜ ↦ Vᵣ])
         (-W¹ Vₗ sₗ)))
     (app $ ℒ (-W¹ (-Clo (list x xᵣ) ⟦e⟧ ρ Γ) sₕ) (list W₁ Wₗ) Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(_ _)
     (error 'app-apply "TODO: ~a ~a" (show-W¹ W₀) (map show-W¹ Wᵢs))]))

(: app-make-sequence : -⟦f⟧)
;; FIXME tmp hack for `make-sequence` use internallyr
(define (app-make-sequence $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (define Vs (list -car -cdr 'values -one -cons? -ff -ff))
  (define s (-@ 'values (list -car -cdr 'values -one -cons? -ff -ff) +ℓ₀))
  (define A (-W Vs s))
  (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))

(: app-opq : -s → -⟦f⟧)
(define ((app-opq sₕ) $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (define sₐ (apply -?@ sₕ (map -W¹-s Ws)))
  (for ([W (in-list Ws)])
    (add-leak! Σ (-W¹-V W)))
  (define αₖ (-ℋ𝒱))
  (define κ (-κ (bgn0.e∷ (-W -●/Vs sₐ) '() ⊥ρ ⟦k⟧) Γ ⟪ℋ⟫ 'void '()))
  (σₖ⊔! Σ αₖ κ)
  {set (-ς↑ αₖ ⊤Γ ⟪ℋ⟫∅)})

(: alloc-init-args! : -Σ -Γ -ρ -⟪ℋ⟫ (Listof Symbol) (Listof -W¹) → -ρ)
(define (alloc-init-args! Σ Γ ρ ⟪ℋ⟫ xs Ws)
  (define ρ₀ (ρ+ ρ -x-dummy (-α->⟪α⟫ (-α.x -x-dummy ⟪ℋ⟫))))
  (for/fold ([ρ : -ρ ρ₀]) ([x xs] [Wₓ Ws])
    (match-define (-W¹ Vₓ sₓ) Wₓ)
    (define α (-α->⟪α⟫ (-α.x x ⟪ℋ⟫)))
    (define Vₓ*
      ;; Refine arguments by type-like contracts before proceeding
      ;; This could save lots of spurious errors to eliminate later
      (V+ (-Σ-σ Σ) Vₓ (predicates-of Γ sₓ)))
    (σ⊕! Σ α Vₓ*)
    
    ;; Debug for `slatex`
    #;(when (and (member x '(raw-filename s₃ filename filename₁))
               (match? Wₓ (-W¹ (? -●?) _)))
      (printf "binding ~a as ~a~n~n" x (show-W¹ Wₓ)))

    (ρ+ ρ x α)))

(: alloc-rest-args! : -Σ -Γ -⟪ℋ⟫ -ℒ (Listof -W¹) → -V)
(define (alloc-rest-args! Σ Γ ⟪ℋ⟫ ℒ Ws)

  (: precise-alloc! ([(Listof -W¹)] [Natural] . ->* . -V))
  ;; Allocate vararg list precisely, preserving length
  (define (precise-alloc! Ws [i 0])
    (match Ws
      [(list) -null]
      [(cons (-W¹ Vₕ sₕ) Ws*)
       (define αₕ (-α->⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ i)))
       (define αₜ (-α->⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ i)))
       (define Vₕ*
         ;; Refine arguments by type-like contracts before proceeding
         ;; This could save lots of spurious errors to eliminate later
         (V+ (-Σ-σ Σ) Vₕ (predicates-of Γ sₕ)))
       (σ⊕*! Σ [αₕ ↦ Vₕ*]
               [αₜ ↦ (precise-alloc! Ws* (+ 1 i))])
       (-Cons αₕ αₜ)]))
  
  ;; Allocate length up to 2 precisely to let `splay` to go through
  ;; This is because `match-lambda*` expands to varargs with specific
  ;; expectation of arities
  (match Ws
    [(or (list) (list _) (list _ _))
     (precise-alloc! Ws)]
    [(? pair?)
     (define αₕ (-α->⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ #f)))
     (define αₜ (-α->⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ #f)))
     (define Vₜ (-Cons αₕ αₜ))
     ;; Allocate spine for var-arg lists
     (σ⊕*! Σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
     ;; Allocate elements in var-arg lists
     (for ([W Ws])
       (match-define (-W¹ Vₕ sₕ) W)
       (σ⊕! Σ αₕ (V+ (-Σ-σ Σ) Vₕ (predicates-of Γ sₕ))))
     Vₜ]))

(: mon : -l³ -$ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (mon l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ C _) W-C)
  (define mon*
    (cond
      [(-=>_? C) mon-=>_]
      [(-St/C? C) mon-struct/c]
      [(-x/C? C) mon-x/c]
      [(-And/C? C) mon-and/c]
      [(-Or/C? C) mon-or/c]
      [(-Not/C? C) mon-not/c]
      [(-Vectorof? C) mon-vectorof]
      [(-Vector/C? C) mon-vector/c]
      [else mon-flat/c]))
  (mon* l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Application
(define/memo (ap∷ [Ws : (Listof -W¹)]
                  [⟦e⟧s : (Listof -⟦e⟧)]
                  [ρ : -ρ]
                  [l : -l]
                  [ℒ : -ℒ]
                  [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define Ws* (cons (-W¹ V s) Ws))
       (match ⟦e⟧s
         ['()
          (match-define (cons Wₕ Wₓs) (reverse Ws*))
          (app $ ℒ Wₕ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
         [(cons ⟦e⟧ ⟦e⟧s*)
          (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ Ws* ⟦e⟧s* ρ l ℒ ⟦k⟧))])]
      [_
       (define blm
         (-blm l 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs))) (-ℒ-app ℒ)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (mon.c∷ [l³ : -l³]
                     [ℒ : -ℒ]
                     [C : (U (Pairof -⟦e⟧ -ρ) -W¹)]
                     [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match-define (-l³ _ _ lo) l³)
  (define root (if (pair? C) (cdr C) C))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define W-V (-W¹ V s))
       (cond [(-W¹? C) (mon l³ $ ℒ C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
             [else
              (match-define (cons ⟦c⟧ ρ) C)
              (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ l³ ℒ W-V ⟦k⟧))])]
      [else
       (define blm (-blm lo 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (mon.v∷ [l³ : -l³]
                     [ℒ : -ℒ]
                     [V : (U (Pairof -⟦e⟧ -ρ) -W¹)]
                     [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match-define (-l³ _ _ lo) l³)
  (define root (if (pair? V) (cdr V) V))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
    (match-define (-W Vs s) A)
    (match Vs
      [(list C)
       (define W-C (-W¹ C s))
       (cond [(-W¹? V) (mon l³ $ ℒ W-C V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
             [else
              (match-define (cons ⟦v⟧ ρ) V)
              (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.c∷ l³ ℒ W-C ⟦k⟧))])]
      [else
       (define blm (-blm lo 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; let-values
(define/memo (let∷ [ℓ : ℓ]
                   [xs : (Listof Symbol)]
                   [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                   [bnd-Ws : (Listof (List Symbol -V -s))]
                   [⟦e⟧ : -⟦e⟧]
                   [ρ : -ρ]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (define n (length xs))
    
    (cond
      [(= n (length Vs))
       (define bnd-Ws*
         (for/fold ([acc : (Listof (List Symbol -V -s)) bnd-Ws])
                   ([x xs] [V Vs] [sₓ (split-values s n)])
           (cons (list x V sₓ) acc)))
       (match ⟦bnd⟧s
         ['()
          (match-define (-Σ σ _ _) Σ)
          (define-values (ρ* Γ*) ; with side effect widening store
            (for/fold ([ρ : -ρ ρ] [Γ : -Γ Γ])
                      ([bnd-W bnd-Ws*])
              (match-define (list (? symbol? x) (? -V? Vₓ) (? -s? sₓ)) bnd-W)
              (define α (-α->⟪α⟫ (-α.x x ⟪ℋ⟫)))
              (σ⊕! Σ α (V+ σ Vₓ (predicates-of Γ sₓ)))
              (values (ρ+ ρ x α) (-Γ-with-aliases Γ x sₓ))))
          (⟦e⟧ ρ* $ Γ* ⟪ℋ⟫ Σ ⟦k⟧)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ $ Γ ⟪ℋ⟫ Σ (let∷ ℓ xs* ⟦bnd⟧s* bnd-Ws* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm (ℓ-src ℓ) 'let-values
               (list (format-symbol "requires ~a values" (length xs)))
               (list (format-symbol "provided ~a values" (length Vs)))
               +ℓ₀))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; begin
(define/memo (bgn∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (rst-Γ∷ Γ (make-memoized-⟦k⟧ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))))]))

;; begin0, waiting on first value
(define/memo (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (rst-Γ∷ Γ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧))))]))

;; begin0, already have first value
(define/memo (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['()
     (with-error-handling (⟦k⟧ _ $ Γ ⟪ℋ⟫ Σ) #:roots (W)
       (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ))]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ _ $ Γ ⟪ℋ⟫ Σ) #:roots (W ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (rst-Γ∷ Γ (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧))))]))

;; clean-up path-condition
(define/memo (rst-Γ∷ [Γ : -Γ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ _ ⟪ℋ⟫ Σ) #:roots ()
    (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(:* mon-=>_ mon-struct/c mon-x/c mon-and/c mon-or/c mon-not/c mon-vectorof mon-vector/c mon-flat/c :
    -l³ -$ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))

(define (mon-=>_ l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ (? -=>_? grd) c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-Σ σ _ M) Σ)

  (: blm : -V → -Γ → (℘ -ς))
  (define ((blm C) Γ)
    (define blm (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  (: chk-arity : -Γ → (℘ -ς))
  (define (chk-arity Γ)
    (define W-grd-arity
      (let* ([a (guard-arity grd)]
             [b (-b a)])
        (-W¹ b b)))
    (define W-arity
      (let ([A (V-arity V)]
            [a (-?@ 'procedure-arity v)])
        (-W¹ (if A (-b A) -●/V) a)))
    (with-MΓ⊢oW (M σ Γ 'arity-includes? W-arity W-grd-arity)
      #:on-t wrap
      #:on-f (let ([C (match W-grd-arity
                        [(-W¹ (-b (? integer? n)) _)
                         (format-symbol "(arity-includes/c ~a)" n)]
                        [(-W¹ (-b (arity-at-least n)) _)
                         (format-symbol "(arity-at-least/c ~a)" n)])])
               (blm C))))

  (: wrap : -Γ → (℘ -ς))
  (define (wrap Γ)
    (define ⟪α⟫ (-α->⟪α⟫ (or (keep-if-const v) (-α.fn ℒ ⟪ℋ⟫ l+ (-Γ-facts Γ)))))
    (define Ar (-Ar grd ⟪α⟫ l³))

    (σ⊕! Σ ⟪α⟫ V)
    (define v* ; hack
      (match v
        [(-ar (== c) _) v]
        [_ (-?ar c v)]))
    (⟦k⟧ (-W (list Ar) v*) $ Γ ⟪ℋ⟫ Σ))

  (with-MΓ⊢oW (M σ Γ 'procedure? W-V)
    #:on-t chk-arity
    #:on-f (blm 'procedure?)))

(define (mon-struct/c l³ $ ℒ Wₚ Wᵥ Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ M) Σ)
  (match-define (-W¹ (and Vₚ (-St/C flat? 𝒾 αℓs)) sₚ) Wₚ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-l³ l+ _ lo) l³)
  (define p (-st-p 𝒾))

  (: chk-fields : -Γ → (℘ -ς))
  (define (chk-fields Γ)
    (define-values (αs ℓs) ((inst unzip ⟪α⟫ ℓ) αℓs))
    (define all-immutable? (struct-all-immutable? 𝒾))

    (define ⟦field⟧s : (Listof -⟦e⟧)
      (for/list ([α (in-list αs)]
                 [i (in-naturals)] #:when (index? i))
        (define ac (-st-ac 𝒾 i))
        (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ (-W¹ ac ac)) (list (mk-rt-⟦e⟧ Wᵥ)))))

    (cond
      [(null? ⟦field⟧s)
       (⟦k⟧ (-W (list (-St 𝒾 '())) sᵥ) $ Γ ⟪ℋ⟫ Σ)]
      [else
       (define cs (-struct/c-split sₚ 𝒾))
       (define K (let ([k (-st-mk 𝒾)]) (-W¹ k k)))
       (define ⟦k⟧* ; maybe wrap the monitored struct
         (cond [all-immutable? ⟦k⟧]
               [else
                (define α (-α->⟪α⟫ (-α.st 𝒾 ℒ ⟪ℋ⟫)))
                (wrap-st∷ Vₚ α l³ ⟦k⟧)]))
       (for/union : (℘ -ς) ([Cs (σ@/list Σ αs)])
          (define ⟦mon⟧s : (Listof -⟦e⟧)
            (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s] [ℓᵢ : ℓ ℓs])
              (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
          (define ⟦reconstr⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ K) ⟦mon⟧s))
          (⟦reconstr⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]))

  (with-MΓ⊢oW (M σ Γ p Wᵥ)
    #:on-t chk-fields
    #:on-f (λ ([Γ : -Γ])
             (define blm (-blm l+ lo (list p) (list Vᵥ) (-ℒ-app ℒ)))
             (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))))

(define (mon-x/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-x/C ⟪α⟫) C)
  (define x (match-let ([(-α.x/c x*) (⟪α⟫->-α ⟪α⟫)])
              (+x!/memo 'mon x*)))
  (define 𝐱 (-x x))
  (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ ℒ))
  (for/set: : (℘ -ς) ([C* (σ@ Σ ⟪α⟫)])
    (define ⟪α⟫ᵥ (-α->⟪α⟫ (-α.x x ⟪ℋ⟫ₑₑ)))
    (define αₖ (-ℳ x l³ ℒ C* ⟪α⟫ᵥ))
    (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ #|FIXME hack|# 'values (list v)))
    (σ⊕! Σ ⟪α⟫ᵥ V)
    (σₖ⊔! Σ αₖ κ)
    (-ς↑ αₖ ⊤Γ ⟪ℋ⟫ₑₑ)))

(define (mon-and/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (match-define (-W¹ (-And/C _ (cons α₁ ℓ₁) (cons α₂ ℓ₂)) c) W-C)
  (match-define (list c₁ c₂) (-app-split c 'and/c 2))
  (for/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
    (mon l³ $ (ℒ-with-mon ℒ ℓ₁) (-W¹ C₁ c₁) W-V Γ ⟪ℋ⟫ Σ 
         (mon.c∷ l³ (ℒ-with-mon ℒ ℓ₂) (-W¹ C₂ c₂) ⟦k⟧))))

(define (mon-or/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ (-Or/C flat? (cons α₁ ℓ₁) (cons α₂ ℓ₂)) c) W-C)
  (define-values (c₁ c₂)
    (match-let ([(list s₁ s₂) (-app-split c 'or/c 2)])
      (values (or s₁ (⟪α⟫->s α₁))
              (or s₂ (⟪α⟫->s α₂)))))
  
  (: chk-or/c : -W¹ ℓ -W¹ ℓ → (℘ -ς))
  (define (chk-or/c W-fl ℓ-fl W-ho ℓ-ho)
    (flat-chk lo $ (ℒ-with-mon ℒ ℓ-fl) W-fl W-V Γ ⟪ℋ⟫ Σ
              (mon-or/c∷ l³ (ℒ-with-mon ℒ ℓ-ho) W-fl W-ho W-V ⟦k⟧)))

  (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
    (define W-C₁ (-W¹ C₁ c₁))
    (define W-C₂ (-W¹ C₂ c₂))
    (cond [(C-flat? C₁) (chk-or/c W-C₁ ℓ₁ W-C₂ ℓ₂)]
          [(C-flat? C₂) (chk-or/c W-C₂ ℓ₂ W-C₁ ℓ₁)]
          [else (error 'or/c "No more than 1 higher-order disjunct for now")])))

(define (mon-not/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ (and C (-Not/C (cons α ℓ*))) c) W-C)
  (match-define (-W¹ V _) W-V)
  (match-define (list c*) (-app-split c 'not/c 1))
  (define ⟦k⟧*
    (let ([⟦ok⟧ (mk-rt-⟦e⟧ W-V)]
          [⟦er⟧ (mk-rt-⟦e⟧ (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)))])
      (if∷ lo ⟦er⟧ ⟦ok⟧ ⊥ρ ⟦k⟧)))
  (for/union : (℘ -ς) ([C* (σ@ (-Σ-σ Σ) α)])
    (assert C* C-flat?)
    (define W-C* (-W¹ C* c*))
    (app $ (ℒ-with-mon ℒ ℓ*) W-C* (list W-V) Γ ⟪ℋ⟫ Σ ⟦k⟧*)))

(define (mon-vectorof l³ $ ℒ Wₚ Wᵥ Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ M) Σ)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-W¹ (and Vₚ (-Vectorof (cons α* ℓ*))) _) Wₚ)

  (: blm : -V → -Γ → (℘ -ς))
  (define ((blm C) Γ)
    (define blm (-blm l+ lo (list C) (list Vᵥ) (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  (: chk-elems : -Γ → (℘ -ς))
  (define (chk-elems Γ)
    (define Wᵥ* ; wrapped vector
      (let ([⟪α⟫ᵥ (-α->⟪α⟫ (-α.unvct ℒ ⟪ℋ⟫ l+))])
        (σ⊕! Σ ⟪α⟫ᵥ Vᵥ)
        (-W (list (-Vector/guard Vₚ ⟪α⟫ᵥ l³)) sᵥ)))
    (define ⟦ref⟧
      (mk-app-⟦e⟧ lo ℒ
                  (mk-rt-⟦e⟧ -vector-ref/W)
                  (list (mk-rt-⟦e⟧ Wᵥ)
                        (mk-rt-⟦e⟧ (-W¹ -Nat/V (-x (+x!/memo 'vof-idx)))))))
    (define ⟦k⟧* (bgn0.e∷ Wᵥ* '() ⊥ρ ⟦k⟧))
    (define c* (⟪α⟫->s α*))
    (for/union : (℘ -ς) ([C* (in-set (σ@ Σ α*))])
      (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓ*) (mk-rt-⟦e⟧ (-W¹ C* c*)) ⟦ref⟧))
      (⟦mon⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧*)))

  (with-MΓ⊢oW (M σ Γ 'vector? Wᵥ)
    #:on-t chk-elems
    #:on-f (blm 'vector?)))

(define (mon-vector/c l³ $ ℒ Wₚ Wᵥ Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ M) Σ)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ (and Vₚ (-Vector/C ⟪α⟫ℓs)) sₚ) Wₚ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (define n (length ⟪α⟫ℓs))
  
  (: blm : -V → -Γ → (℘ -ς))
  (define ((blm C) Γ)
    (define blm (-blm l+ lo (list C) (list Vᵥ) (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  (: chk-len : -Γ → (℘ -ς))
  (define (chk-len Γ)
    (define Wₙ (vec-len σ Γ Wᵥ))
    (define N (let ([bₙ (-b n)]) (-W¹ bₙ bₙ)))
    (with-MΓ⊢oW (M σ Γ '= Wₙ N)
      #:on-t chk-flds
      #:on-f (blm (format-symbol "vector-length/c ~a" n))))

  (: chk-flds : -Γ → (℘ -ς))
  (define (chk-flds Γ)
    (define-values (⟪α⟫s ℓs) (unzip ⟪α⟫ℓs))
    
    (define cs : (Listof -s)
      (for/list ([s (in-list (-app-split sₚ 'vector/c n))]
                 [⟪α⟫ : ⟪α⟫ (in-list ⟪α⟫s)])
        (or s (⟪α⟫->s ⟪α⟫))))

    (for/union : (℘ -ς) ([Cs (in-set (σ@/list σ ⟪α⟫s))])
       (define ⟦mon-fld⟧s : (Listof -⟦e⟧)
         (for/list ([Cᵢ (in-list Cs)]
                    [cᵢ (in-list cs)]
                    [ℓᵢ (in-list ℓs)]
                    [i (in-naturals)] #:when (index? i))
           (define Wᵢ (let ([bᵢ (-b i)]) (-W¹ bᵢ bᵢ)))
           (define Wₚᵢ (-W¹ Cᵢ cᵢ))
           (define ⟦ref⟧
             (mk-app-⟦e⟧ lo ℒ
                         (mk-rt-⟦e⟧ -vector-ref/W)
                         (list (mk-rt-⟦e⟧ Wᵥ) (mk-rt-⟦e⟧ Wᵢ))))
           (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ Wₚᵢ) ⟦ref⟧)))
       (define Wᵥ*
         (let ([⟪α⟫ᵥ (-α->⟪α⟫ (-α.unvct ℒ ⟪ℋ⟫ l+))])
           (σ⊕! Σ ⟪α⟫ᵥ Vᵥ)
           (-W (list (-Vector/guard Vₚ ⟪α⟫ᵥ l³)) sᵥ)))
       (match ⟦mon-fld⟧s
         ['() (⟦k⟧ Wᵥ* $ Γ ⟪ℋ⟫ Σ)]
         [(cons ⟦fld⟧₀ ⟦fld⟧s)
          (⟦fld⟧₀ ⊥ρ $ Γ ⟪ℋ⟫ Σ (bgn0.e∷ Wᵥ* ⟦fld⟧s ⊥ρ ⟦k⟧))])))

  (with-MΓ⊢oW (M σ Γ 'vector? Wᵥ)
    #:on-t chk-len
    #:on-f (blm 'vector?)))

(define (mon-flat/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (define cv (-?@ c v))
  (case (MΓ⊢V∈C (-Σ-M Σ) (-Σ-σ Σ) Γ W-V W-C)
    [(✓) (⟦k⟧ (-W (list V) v) $ (Γ+ Γ cv) ⟪ℋ⟫ Σ)]
    [(✗) (⟦k⟧ (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)) $ (Γ+ Γ (-not cv)) ⟪ℋ⟫ Σ)]
    [(?)
     (app $ ℒ W-C (list W-V) Γ ⟪ℋ⟫ Σ
          (if.flat/c∷ (-W (list V) v) (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)) ⟦k⟧))]))

(: flat-chk : -l -$ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (flat-chk l $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ σₖ _) Σ)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match C
    [(-And/C _ (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (define-values (c₁ c₂)
       (match-let ([(list s₁ s₂) (-app-split c 'and/c 2)])
         (values (or s₁ (⟪α⟫->s α₁)) (or s₂ (⟪α⟫->s α₂)))))
     [for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       (define W-C₁ (-W¹ C₁ c₁))
       (define W-C₂ (-W¹ C₂ c₂))
       (flat-chk l $ (ℒ-with-mon ℒ ℓ₁) W-C₁ W-V Γ ⟪ℋ⟫ Σ
                 (fc-and/c∷ l (ℒ-with-mon ℒ ℓ₂) W-C₁ W-C₂ ⟦k⟧))]]
    [(-Or/C _ (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (define-values (c₁ c₂)
       (match-let ([(list s₁ s₂) (-app-split c 'or/c 2)])
         (values (or s₁ (⟪α⟫->s α₁)) (or s₂ (⟪α⟫->s α₂)))))
     (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       (define W-C₁ (-W¹ C₁ c₁))
       (define W-C₂ (-W¹ C₂ c₁))
       (flat-chk l $ (ℒ-with-mon ℒ ℓ₁) W-C₁ W-V Γ ⟪ℋ⟫ Σ
                 (fc-or/c∷ l (ℒ-with-mon ℒ ℓ₂) W-C₁ W-C₂ W-V ⟦k⟧)))]
    [(-Not/C (cons α ℓ*))
     (define c*
       (match-let ([(list s) (-app-split c 'not/c 1)])
         (or s (⟪α⟫->s α))))
     (for/union : (℘ -ς) ([C* (σ@ σ α)])
       (define W-C* (-W¹ C* c*))
       (flat-chk l $ (ℒ-with-mon ℒ ℓ*) W-C* W-V Γ ⟪ℋ⟫ Σ (fc-not/c∷ l W-C* W-V ⟦k⟧)))]
    [(-St/C _ s αℓs)
     (define-values (αs ℓs) ((inst unzip ⟪α⟫ ℓ) αℓs))
     (define cs
       (let ([ss (-struct/c-split c s)])
         (for/list : (Listof -s) ([s ss] [α : ⟪α⟫ αs])
           (or s (⟪α⟫->s α)))))
     (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
       (define ⟦chk-field⟧s : (Listof -⟦e⟧)
         (for/list ([Cᵢ (in-list Cs)]
                    [cᵢ (in-list cs)]
                    [ℓᵢ : ℓ (in-list ℓs)]
                    [i (in-naturals)] #:when (index? i))
           (define ac (-st-ac s i))
           (define ⟦ref⟧ᵢ (mk-app-⟦e⟧ 'Λ ℒ (mk-rt-⟦e⟧ (-W¹ ac ac)) (list (mk-rt-⟦e⟧ W-V))))
           (mk-fc-⟦e⟧ l (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ (-W¹ Cᵢ cᵢ)) ⟦ref⟧ᵢ)))
       (match ⟦chk-field⟧s
         ['()
          (define p (-st-p s))
          (define ⟦rt⟧ (mk-rt-⟦e⟧ (-W (list -tt (V+ σ V p)) (-?@ 'values -tt v))))
          (app $ ℒ (-W¹ p p) (list W-V) Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ ⟦ff⟧ ⊥ρ ⟦k⟧))]
         [(cons ⟦chk-field⟧ ⟦chk-field⟧s*)
          (⟦chk-field⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (fc-struct/c∷ l ℒ s '() ⟦chk-field⟧s* ⊥ρ ⟦k⟧))]))]
    [(-x/C ⟪α⟫)
     (define x (match-let ([(-α.x/c x*) (⟪α⟫->-α ⟪α⟫)])
                 (+x!/memo 'fc x*)))
     (define 𝐱 (-x x))
     (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ ℒ))
     (for/set: : (℘ -ς) ([C* (σ@ σ ⟪α⟫)])
       (define ⟪α⟫ᵥ (-α->⟪α⟫ (-α.x x ⟪ℋ⟫ₑₑ)))
       (define αₖ (-ℱ x l ℒ C* ⟪α⟫ᵥ))
       (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ #|FIXME hack #f? instead?|# 'fc (list v)))
       (σ⊕! Σ ⟪α⟫ᵥ V)
       (σₖ⊔! Σ αₖ κ)
       (-ς↑ αₖ ⊤Γ ⟪ℋ⟫ₑₑ))]
    [_
     (define ⟦ap⟧ (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W-C) (list (mk-rt-⟦e⟧ W-V))))
     (define ⟦rt⟧ (mk-rt-⟦e⟧ (-W (list -tt (V+ σ V C)) (-?@ 'values -tt v))))
     (⟦ap⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ ⟦ff⟧ ⊥ρ ⟦k⟧))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helper frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memo (mon-or/c∷ [l³ : -l³]
                        [ℒ : -ℒ]
                        [Wₗ : -W¹]
                        [Wᵣ : -W¹]
                        [W-V : -W¹]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Wₗ Wᵣ W-V)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (mon l³ $ ℒ Wᵣ W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(list (-b #t) V)
       (match-define (-W¹ Cₗ _) Wₗ)
       (define v*
         (match s
           [(-@ 'values (list _ v) _) v]
           [#f #f]))
       (⟦k⟧ (-W (list (V+ (-Σ-σ Σ) V Cₗ)) v*) $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (if.flat/c∷ [W-V : -W] [blm : -blm] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-V)
    (match-define (-W Vs v) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V v)])
         #:true  (⟦k⟧ W-V $ Γ₁ ⟪ℋ⟫ Σ)
         #:false (⟦k⟧ blm $ Γ₂ ⟪ℋ⟫ Σ))]
      [_
       (match-define (-blm _ lo _ _ ℓ) blm)
       (⟦k⟧ (-blm lo 'Λ '(|1 value|) Vs ℓ) $ Γ ⟪ℋ⟫ Σ)])))

;; Conditional
(define/memo (if∷ [l : -l] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V s)])
         #:true  (⟦e⟧₁ ρ $ Γ₁ ⟪ℋ⟫ Σ ⟦k⟧)
         #:false (⟦e⟧₂ ρ $ Γ₂ ⟪ℋ⟫ Σ ⟦k⟧))]
      [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs))) +ℓ₀) $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (and∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (if∷ l ⟦e⟧ ⟦ff⟧ ρ (and∷ l ⟦e⟧s* ρ ⟦k⟧))]))

(define/memo (or∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*) ; TODO propagate value instead
     (if∷ l ⟦tt⟧ ⟦e⟧ ρ (or∷ l ⟦e⟧s* ρ ⟦k⟧))]))

(define/memo (neg∷ [l : -l] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧ (if∷ l ⟦ff⟧ ⟦tt⟧ ⊥ρ ⟦k⟧))

(define/memo (wrap-st∷ [C : -St/C]
                       [⟪α⟫ᵤ : ⟪α⟫]
                       [l³ : -l³]
                       [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (define V* (-St* C ⟪α⟫ᵤ l³))
  (define ⟪α⟫-casted #|FIXME TR|# (cast ⟪α⟫ᵤ (Rec X (U -V -W -W¹ -ρ ⟪α⟫ (Listof X) (℘ X)))))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (C ⟪α⟫-casted)
    (match-define (-W Vs s) A)
    (match-define (list V) Vs) ; only used internally, should be safe
    (σ⊕! Σ ⟪α⟫ᵤ V)
    (⟦k⟧ (-W (list V*) s) $ Γ ⟪ℋ⟫ Σ)))

(define/memo (fc-and/c∷ [l : -l]
                        [ℒ : -ℒ]
                        [W-C₁ : -W¹]
                        [W-C₂ : -W¹]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f)) (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)]
      [(list (-b #t) V)
       (match-define (-@ 'values (list _ sᵥ) _) s)
       (match-define (-W¹ C₁ _) W-C₁)
       (flat-chk l $ ℒ W-C₂ (-W¹ (V+ (-Σ-σ Σ) V C₁) sᵥ) Γ ⟪ℋ⟫ Σ ⟦k⟧)])))

(define/memo (fc-or/c∷ [l : -l]
                       [ℒ : -ℒ]
                       [W-C₁ : -W¹]
                       [W-C₂ : -W¹]
                       [W-V : -W¹]
                       [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (flat-chk l $ ℒ W-C₂ W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(list (-b #t) V)
       (match-define (-W¹ C₁ _) W-C₁)
       (⟦k⟧ (-W (list -tt (V+ (-Σ-σ Σ) V C₁)) s) $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (fc-not/c∷ [l : -l]
                        [W-C* : -W¹]
                        [W-V : -W¹]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C* W-V)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (match-define (-W¹ V v) W-V)
       (⟦k⟧ (-W (list -tt V) (-?@ 'values -tt v)) $ Γ ⟪ℋ⟫ Σ)]
      [(list (-b #t) V)
       (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (fc-struct/c∷ [l : -l]
                           [ℒ : -ℒ]
                           [𝒾 : -𝒾]
                           [W-Vs-rev : (Listof -W¹)]
                           [⟦e⟧s : (Listof -⟦e⟧)]
                           [ρ : -ρ]
                           [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-Vs-rev ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)]
      [(list (-b #t) V*)
       (define v*
         (match s
           [(-@ 'values (list _ v) _) v]
           [#f #f]))
       (match ⟦e⟧s
         ['()
          (define ⟦k⟧*
            (let ([k (-st-mk 𝒾)])
              (ap∷ (append W-Vs-rev (list (-W¹ k k))) '() ⊥ρ l ℒ
                   (ap∷ (list (-W¹ -tt -tt) (-W¹ 'values 'values)) '() ⊥ρ l ℒ ⟦k⟧))))
          (⟦k⟧* (-W (list V*) v*) $ Γ ⟪ℋ⟫ Σ)]
         [(cons ⟦e⟧ ⟦e⟧s*)
          (define W* (-W¹ V* v*))
          (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc-struct/c∷ l ℒ 𝒾 (cons W* W-Vs-rev) ⟦e⟧s* ρ ⟦k⟧))])])))

(define/memo (fc.v∷ [l : -l]
                    [ℒ : -ℒ]
                    [⟦v⟧ : -⟦e⟧]
                    [ρ : -ρ]
                    [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list C)
       (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.c∷ l ℒ (-W¹ C s) ⟦k⟧))]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (fc.c∷ [l : -l]
                    [ℒ : -ℒ]
                    [W-C : -W¹]
                    [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (flat-chk l $ ℒ W-C (-W¹ V s) Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helper expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memo (mk-mon-⟦e⟧ [l³ : -l³] [ℒ : -ℒ] [⟦c⟧ : -⟦e⟧] [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ l³ ℒ (cons ⟦e⟧ ρ) ⟦k⟧))))

(define/memo (mk-app-⟦e⟧ [l : -l] [ℒ : -ℒ] [⟦f⟧ : -⟦e⟧] [⟦x⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦f⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ '() ⟦x⟧s ρ l ℒ ⟦k⟧))))

(define/memo (mk-rt-⟦e⟧ [A : (U -A -W¹)]) : -⟦e⟧
  (match A
    [(-W¹ V v) (mk-rt-⟦e⟧ (-W (list V) v))]
    [(? -A?) (λ (_ $ Γ ⟪ℋ⟫ Σ ⟦k⟧) (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))]))

(define/memo (mk-erase-⟦e⟧ [⟪α⟫s : (Listof ⟪α⟫)]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (for ([⟪α⟫ : ⟪α⟫ ⟪α⟫s])
      (σ⊕! Σ ⟪α⟫ -●/V #:mutating? #t))
    (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)))

(define/memo (mk-begin-⟦e⟧ [⟦e⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
  (match ⟦e⟧s
    ['() ⟦void⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))

(define/memo (mk-if-⟦e⟧ [l : -l]
                       [⟦e⟧₁ : -⟦e⟧]
                       [⟦e⟧₂ : -⟦e⟧]
                       [⟦e⟧₃ : -⟦e⟧]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦e⟧₁ ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦e⟧₂ ⟦e⟧₃ ρ ⟦k⟧))))

(define/memo (mk-fc-⟦e⟧ [l : -l]
                       [ℒ : -ℒ]
                       [⟦c⟧ : -⟦e⟧]
                       [⟦v⟧ : -⟦e⟧]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.v∷ l ℒ ⟦v⟧ ρ ⟦k⟧))))

(define/memo (make-memoized-⟦k⟧ [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (define-type Key (List -A -Γ -⟪ℋ⟫))
  (define-type Rec (List (HashTable ⟪α⟫ (℘ -V)) (℘ -ς)))
  (let ([m : (HashTable Key Rec) (make-hash)])
    (define ⟦k⟧* : -⟦k⟧
      (λ (A $ Γ ⟪ℋ⟫ Σ)
        (match-define (-Σ (-σ mσ _ _) _ _) Σ)
        (define key (list A Γ ⟪ℋ⟫))
        
        (: recompute! : → (℘ -ς))
        (define (recompute!)
          (define ans (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))
          (hash-set! m key (list mσ ans))
          ans)

        ;; Cache result based on rest of components
        (cond [(hash-ref m key #f) =>
               (λ ([rec : Rec])
                 (match-define (list mσ₀ ςs₀) rec)
                 (define root : (℘ ⟪α⟫)
                   (∪ (⟦k⟧->roots ⟦k⟧)
                      (match A
                        [(-W Vs _) (->⟪α⟫s Vs)]
                        [_ ∅eq])))
                 (cond [(map-equal?/spanning-root mσ₀ mσ root V->⟪α⟫s)
                        #;(printf "hit-k~n")
                        ςs₀]
                       [else (recompute!)]))]
              [else (recompute!)])))
    (add-⟦k⟧-roots! ⟦k⟧* (⟦k⟧->roots ⟦k⟧))
    (set-⟦k⟧->αₖ! ⟦k⟧* (⟦k⟧->αₖ ⟦k⟧))
    ⟦k⟧*))
