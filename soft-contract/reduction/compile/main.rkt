#lang typed/racket/base

(provide ↓ₚ ↓ₘ ↓ₑ)

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/widen.rkt"
         "base.rkt"
         "kontinuation.rkt"
         racket/set
         racket/match)

(: ↓ₚ : (Listof -module) -e → -⟦e⟧)
;; Compile program
(define (↓ₚ ms e)
  (define ⟦e⟧ (↓ₑ '† e))
  (match (map ↓ₘ ms)
    ['() ⟦e⟧]
    [(cons ⟦m⟧ ⟦m⟧s)
     (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
       (⟦m⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ `(,@⟦m⟧s ,⟦e⟧) ρ ⟦k⟧)))]))

(: ↓ₘ : -module → -⟦e⟧)
;; Compile module
(define (↓ₘ m)
  (match-define (-module l ds) m)

  (: ↓pc : -provide-spec → -⟦e⟧)
  (define (↓pc spec)
    (match-define (-p/c-item x c ℓ) spec)
    (define ⟦c⟧ (↓ₑ l c))
    (define 𝒾 (-𝒾 x l))
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (dec∷ ℓ 𝒾 ⟦k⟧))))
  
  (: ↓d : -module-level-form → -⟦e⟧)
  (define (↓d d)
    (match d
      [(-define-values xs e)
       (define αs : (Listof ⟪α⟫) (for/list ([x xs]) (-α->⟪α⟫ (-𝒾 x l))))
       (define ⟦e⟧ (↓ₑ l e))
       (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
         (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (def∷ l αs ⟦k⟧)))]
      [(-provide specs)
       (match (map ↓pc specs)
         ['() ⟦void⟧]
         [(cons ⟦spec⟧ ⟦spec⟧s)
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦spec⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦spec⟧s ρ ⟦k⟧)))])]
      [(? -e? e) (↓ₑ l e)]
      [_
       (log-warning "↓d : ignore ~a~n" (show-module-level-form d))
       ⟦void⟧]))

  (match (map ↓d ds)
    ['() ⟦void⟧]
    [(cons ⟦d⟧ ⟦d⟧s)
     (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
       (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦d⟧s ρ ⟦k⟧)))]))

(: ↓ₑ : -l -e → -⟦e⟧)
;; Compile expression to computation
(define (↓ₑ l e)

  (define (↓ [e : -e]) (↓ₑ l e))

  (remember-e!
   (match e
     [(-λ xs e*)
      (define ⟦e*⟧ (make-memoized-⟦e⟧ (↓ e*)))
      (define fvs (fv e*))
      #;(printf "Warning: no longer canonicalize λ-term~n")
      (define t (-λ xs e*))
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (define ρ* (m↓ ρ fvs))
        (define Γ*
          (match-let ([(-Γ φs as) Γ])
            (define φs*
              (for*/set: : (℘ -t) ([φ φs]
                                   [fv⟦φ⟧ (in-value (fvₜ φ))]
                                   #:unless (set-empty? fv⟦φ⟧)
                                   #:when (⊆ fv⟦φ⟧ fvs))
                φ))
            (define as* #|TODO|# as)
            (-Γ φs* as*)))
        (⟦k⟧ (-W (list (-Clo xs ⟦e*⟧ ρ* Γ*)) t) $ Γ ⟪ℋ⟫ Σ))]
     [(-case-λ clauses)
      (define ⟦clause⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))
        (for/list ([clause clauses])
          (match-define (cons xs e) clause)
          (cons xs (↓ e))))
      (define t (-case-λ clauses))
      #;(printf "Warning: no longer canonicalize λ-term~n")
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦k⟧ (-W (list (-Case-Clo ⟦clause⟧s ρ Γ)) t) $ Γ ⟪ℋ⟫ Σ))]
     [(? -prim? p) (↓ₚᵣₘ p)]
     [(-•)
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦k⟧ -●.W $ Γ ⟪ℋ⟫ Σ))]
     [(-x x) (↓ₓ l x)]
     [(and 𝒾 (-𝒾 x l₀))

      (define-values (α modify-V)
        (cond
          ;; same-module referencing returns unwrapped version
          [(equal? l₀ l)
           (values 𝒾 (inst values -V))]
          ;; cross-module referencing returns wrapped version
          ;; when the caller is symbolic (HACK)
          ;; and supplies the negative monitoring context (HACK)
          [(symbol? l)
           (values (-α.wrp 𝒾) (λ ([V : -V]) (with-negative-party l V)))]
          ;; cross-mldule referencing returns abstracted wrapped version
          ;; when the caller is concrete (HACK)
          ;; and supplies the negative monitoring context (HACK)
          [else
           (values (-α.wrp 𝒾) (λ ([V : -V])
                                (with-positive-party 'dummy+
                                  (with-negative-party l
                                    (approximate-under-contract V)))))]))
      
      (define ⟪α⟫ (-α->⟪α⟫ α))

      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (define s (and (not (mutated? Σ ⟪α⟫)) 𝒾))
        (cond
          [($@ $ (or s 𝒾)) =>
           (λ ([V : -V])
             (⟦k⟧ (-W (list V) s) $ Γ ⟪ℋ⟫ Σ))]
          [else
           (unless (hash-has-key? (-σ-m (-Σ-σ Σ)) ⟪α⟫ₒₚ) ; HACK
             (σ⊕V! Σ ⟪α⟫ₒₚ -●.V))
           (for/union : (℘ -ς) ([V (in-set (σ@ Σ ⟪α⟫))])
             (define V* (modify-V V))
             (define $* ($+ $ (or s 𝒾) V*))
             (⟦k⟧ (-W (list V*) s) $* Γ ⟪ℋ⟫ Σ))]))]
     
     [(-@ f xs ℓ)
      (define ⟦f⟧  (↓ f))
      (define ⟦x⟧s (map ↓ xs))
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦f⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ '() ⟦x⟧s ρ (-ℒ ∅eq ℓ) ⟦k⟧)))]
     [(-if e₀ e₁ e₂)
      (define ⟦e₀⟧ (↓ e₀))
      (define ⟦e₁⟧ (↓ e₁))
      (define ⟦e₂⟧ (↓ e₂))
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦e₀⟧ ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
     [(-wcm k v b) (error '↓ₑ "TODO: wcm")]
     [(-begin es)
      (match (map ↓ es)
        ['()
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦k⟧ -void.W $ Γ ⟪ℋ⟫ Σ))]
        [(cons ⟦e⟧ ⟦e⟧s)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (make-memoized-⟦k⟧ (bgn∷ ⟦e⟧s ρ ⟦k⟧))))])]
     [(-begin0 e₀ es)
      (define ⟦e₀⟧ (↓ e₀))
      (define ⟦e⟧s (map ↓ es))
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦e₀⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn0.v∷ ⟦e⟧s ρ ⟦k⟧)))]
     [(-quote q)
      (cond
        [(Base? q)
         (define W (let ([b (-b q)]) (-W (list b) b)))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ))]
        [else (error '↓ₑ "TODO: (quote ~a)" q)])]
     [(-let-values bnds e* ℓ)
      (define ⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))
        (for/list ([bnd bnds])
          (match-define (cons xs eₓₛ) bnd)
          (cons xs (↓ eₓₛ))))
      (define ⟦e*⟧ (↓ e*))
      (match ⟦bnd⟧s
        ['() ⟦e*⟧]
        [(cons (cons xs ⟦e⟧ₓₛ) ⟦bnd⟧s*)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦e⟧ₓₛ ρ $ Γ ⟪ℋ⟫ Σ (let∷ ℓ xs ⟦bnd⟧s* '() ⟦e*⟧ ρ ⟦k⟧)))])]
     [(-letrec-values bnds e* ℓ)
      (define ⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))
        (for/list ([bnd bnds])
          (match-define (cons xs eₓₛ) bnd)
          (cons xs (↓ eₓₛ))))
      (define ⟦e*⟧ (↓ e*))
      (match ⟦bnd⟧s
        ['() ⟦e*⟧]
        [(cons (cons xs ⟦e⟧ₓₛ) ⟦bnd⟧s*)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (define ρ* ; with side effect widening store
             (for*/fold ([ρ  : -ρ  ρ])
                        ([⟦bnd⟧ ⟦bnd⟧s]
                         [xs (in-value (car ⟦bnd⟧))]
                         [x xs])
               (define α (-α->⟪α⟫ (-α.x x ⟪ℋ⟫ #|TODO|# ∅)))
               (σ⊕V! Σ α -undefined)
               (ρ+ ρ x α)))
           (⟦e⟧ₓₛ ρ* $ Γ ⟪ℋ⟫ Σ
            (letrec∷ ℓ xs ⟦bnd⟧s* ⟦e*⟧ ρ* ⟦k⟧)))])]
     [(-set! x e*)
      (define ⟦e*⟧ (↓ e*))
      (match x
        [(-x x)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦e*⟧ ρ $ Γ ⟪ℋ⟫ Σ (set!∷ (ρ@ ρ x) ⟦k⟧)))]
        [(? -𝒾? 𝒾)
         (define α (-α->⟪α⟫ 𝒾))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦e*⟧ ρ $ Γ ⟪ℋ⟫ Σ (set!∷ α ⟦k⟧)))])]
     [(-error msg ℓ)
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦k⟧ (-blm (ℓ-src ℓ) 'Λ '() (list (-b msg)) ℓ) $ Γ ⟪ℋ⟫ Σ))]
     [(-μ/c x c)
      (define ⟦c⟧ (↓ c))
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (μ/c∷ x ⟦k⟧)))]
     [(--> cs d ℓ)
      (define ⟦d⟧  (↓ d))
      (match (-var-map ↓ cs)
        ['()
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ '() #f ℓ ⟦k⟧)))]
        [(cons ⟦c⟧ ⟦c⟧s)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ '() ⟦c⟧s #f ⟦d⟧ ρ ℓ ⟦k⟧)))]
        [(-var ⟦c⟧s ⟦c⟧ᵣ)
         (match ⟦c⟧s
           ['()
            (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
              (⟦c⟧ᵣ ρ $ Γ ⟪ℋ⟫ Σ (-->.rst∷ '() ⟦d⟧ ρ ℓ ⟦k⟧)))]
           [(cons ⟦c⟧ ⟦c⟧s*)
            (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
              (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ '() ⟦c⟧s* ⟦c⟧ᵣ ⟦d⟧ ρ ℓ ⟦k⟧)))])])]
     [(-->i cs (and mk-d (-λ xs d)) ℓ)
      (define ⟦d⟧ (↓ d))
      (match (map ↓ cs)
        ['()
         (define c (-?->i '() mk-d))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (define Mk-D (-Clo xs ⟦d⟧ ρ Γ))
           (define-values (G g) (mk-=>i! Σ Γ ⟪ℋ⟫ '() Mk-D mk-d ℓ))
           (⟦k⟧ (-W (list G) g) $ Γ ⟪ℋ⟫ Σ))]
        [(cons ⟦c⟧ ⟦c⟧s)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (define Mk-D (-Clo xs ⟦d⟧ ρ Γ))
           (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->i∷ '() ⟦c⟧s ρ Mk-D mk-d ℓ ⟦k⟧)))])]
     [(-case-> clauses ℓ)
      (define ⟦clause⟧s : (Listof (Listof -⟦e⟧))
        (for/list ([clause clauses])
          (match-define (cons cs d) clause)
          `(,@(map ↓ cs) ,(↓ d))))
      (match ⟦clause⟧s
        ['()
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦k⟧ (-W (list (-Case-> '() ℓ)) #f #;e) $ Γ ⟪ℋ⟫ Σ))]
        [(cons (cons ⟦c⟧ ⟦c⟧s) ⟦clause⟧s*)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (case->∷ ℓ '() '() ⟦c⟧s ⟦clause⟧s* ρ ⟦k⟧)))])]
     [(-x/c x)
      (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (⟦k⟧ (-W (list (-x/C (-α->⟪α⟫ (-α.x/c x)))) #f #;e) $ Γ ⟪ℋ⟫ Σ))]
     [(-struct/c 𝒾 cs ℓ)
      (match (map ↓ cs)
        ['()
         (define W (-W (list (-St/C #t 𝒾 '())) (-t.@ (-st/c.mk 𝒾) '())))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ))]
        [(cons ⟦c⟧ ⟦c⟧s)
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (struct/c∷ ℓ 𝒾 '() ⟦c⟧s ρ ⟦k⟧)))])]
     [_ (error '↓ₑ "unhandled: ~a" (show-e e))])
   e))

(: make-memoized-⟦e⟧ : -⟦e⟧ → -⟦e⟧)
(define (make-memoized-⟦e⟧ ⟦e⟧)
  (define-type Key (List -⟪ℋ⟫ -ρ -Γ))
  (define-type Rec (List (HashTable ⟪α⟫ (℘ -V)) (℘ -ς)))
  (let ([m : (HashTable Key Rec) (make-hash)])
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match-define (-Σ (-σ mσ _ _) _ _) Σ)
      (define key : Key (list ⟪ℋ⟫ ρ Γ))

      (: recompute! : → (℘ -ς))
      (define (recompute!)
        (define ans (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧))
        (hash-set! m key (list mσ ans))
        ans)

      ;; Cache result based on rest of components
      (cond [(hash-ref m key #f) =>
             (λ ([rec : Rec])
               (match-define (list mσ₀ ςs₀) rec)
               (cond [(map-equal?/spanning-root mσ₀ mσ (ρ->⟪α⟫s ρ) V->⟪α⟫s)
                      #;(printf "hit-e: ~a~n" (show-⟦e⟧ ⟦e⟧))
                      ςs₀]
                     [else (recompute!)]))]
            [else (recompute!)]))))
