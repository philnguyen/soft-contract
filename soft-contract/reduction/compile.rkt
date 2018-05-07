#lang typed/racket/base

(provide compile@)

(require (only-in racket/function const)
         racket/set
         racket/list
         racket/match
         typed/racket/unit
         set-extras
         unreachable
         abstract-compilation
         (only-in typed-racket-hacks procedure-rename)
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit compile@
  (import meta-functions^ static-info^ ast-pretty-print^
          env^ val^ sto^ evl^ pretty-print^
          step^ alloc^
          prover^)
  (export compile^)

  (: ↓ₚ : -prog → ⟦E⟧)
  ;; Compile program
  (define (↓ₚ p)
    (rn (match (-prog-_0 p)
          ['() (mk-W '())]
          [(cons m ms)
           (define ⟦m⟧ (↓ₘ m))
           (define ⟦m⟧s (map ↓ₘ ms))
           (cond [(null? ⟦m⟧s) ⟦m⟧]
                 [else (λ (Ρ Φ^ Ξ Σ) (⟦m⟧ Ρ Φ^ (K+ (F:Bgn ⟦m⟧s Ρ) Ξ) Σ))])])
        p))

  (: ↓ₘ : -module → ⟦E⟧)
  ;; Compile module
  (define (↓ₘ m)
    (match-define (-module l ds) m)

    (: ↓pc : -provide-spec → ⟦E⟧)
    (define-compiler ((↓pc spec) Ρ Φ^ Ξ Σ)
      ;; Wrap contract
      [=> (-p/c-item x C ℓ)
          (⟦C⟧ Ρ Φ^ (K+ (F:Dec ℓ 𝒾) Ξ) Σ)
          #:where
          [𝒾 (-𝒾 x l)]
          [⟦C⟧ (↓ₑ l C)]]
      ;; Export same as internal
      [=> (? symbol? x)
          (begin (assert (defined-at? Σ α))
                 (⊔ᵥ! Σ α* (Σᵥ@ Σ α))
                 (ret! (R '() Φ^) Ξ Σ))
       #:where
       [α  (mk-α (-α:top (-𝒾 x l)))]
       [α* (mk-α (-α:wrp (-𝒾 x l)))]])
    
    (: ↓d : -module-level-form → ⟦E⟧)
    (define-compiler ((↓d d) Ρ Φ^ Ξ Σ)
      [=> (-define-values xs E)
          (⟦E⟧ Ρ Φ^ (K+ (F:Def l αs) Ξ) Σ)
          #:where
          [αs (for/list : (Listof α) ([x (in-list xs)]) (mk-α (-α:top (-𝒾 x l))))]
          [⟦E⟧ (↓ₑ l E)]]
      [(-provide '()) (mk-W '())]
      [(-provide (list spec)) (↓pc spec)]
      [=> (-provide (cons spec specs))
          (⟦spec⟧ Ρ Φ^ (K+ (F:Bgn (assert ⟦spec⟧s pair?) Ρ) Ξ) Σ)
          #:where
          [⟦spec⟧ (↓pc spec)]
          [⟦spec⟧s (map ↓pc specs)]]
      [(? -e? E) (↓ₑ l E)]
      [_ (begin0 (mk-W '())
           (log-warning "↓d: ignore ~a~n" d))])

    (rn (match ds
          ['() (mk-W '())]
          [(cons D Ds)
           (define ⟦D⟧ (↓d D))
           (define ⟦D⟧s (map ↓d Ds))
           (cond [(null? ⟦D⟧s) ⟦D⟧]
                 [else (λ (Ρ Φ^ Ξ Σ)
                         (⟦D⟧ Ρ Φ^ (K+ (F:Bgn ⟦D⟧s Ρ) Ξ) Σ))])])
        m))

  (: ↓ₑ : -l -e → ⟦E⟧)
  (define (↓ₑ l e)
    (define ↓-bnd : ((Pairof (Listof Symbol) -e) → (Pairof (Listof Symbol) ⟦E⟧))
      (match-lambda
        [(cons x eₓ) (cons x (↓ eₓ))]))

    (define ↓-dom : (-dom → ⟦dom⟧)
      (match-lambda
        [(-dom xs ?dep e ℓ) (⟦dom⟧ xs ?dep (↓ e) ℓ)]))

    (: init-undefined! : Σ (Assoc (Listof Symbol) -e) H Ρ → Ρ)
    (define (init-undefined! Σ bnds H Ρ₀)
      (for*/fold ([Ρ : Ρ Ρ₀]) ([bnd (in-list bnds)] [x (in-list (car bnd))])
        (define α (mk-α (-α:x x H)))
        (⊔ᵥ! Σ α -undefined)
        (Ρ+ Ρ x α)))

    (: struct-defined? : -𝒾 → Σ → Boolean)
    (define (struct-defined? 𝒾)
      (if (member 𝒾 (list -𝒾-cons -𝒾-box))
          (λ _ #t)
          (let ([α (mk-α (-α:top 𝒾))])
            (λ (Σ) (defined-at? Σ α)))))

    (define (blm:undefined-struct [𝒾 : -𝒾] [ℓ : ℓ])
      (Blm (strip-ℓ ℓ) 'Λ '(struct-defined?) (list {set (-𝒾-name 𝒾)})))

    (define (↓/rn [E : -e]) : ⟦E⟧ (rn (↓ E) E))
    
    (: ↓ : -e → ⟦E⟧)
    (define-compiler ((↓ E) Ρ Φ^ Ξ Σ)
      [(? -prim? p) (mk-T p)]
      [(-•) (mk-T (-● ∅))]
      [(-x (? symbol? x) ℓₓ) (↓ₓ x ℓₓ)]
      [=> (-λ xs E*)
          (ret! (T->R (Clo xs ⟦E*⟧ (m↓ Ρ fvs)) Φ^) Ξ Σ)
          #:where
          [fvs (fv E)]
          [⟦E*⟧ (↓/rn E*)]]
      [=> (-x (and 𝒾 (-𝒾 x lₒ)) _)
          (let ([V^ (map/set modify-V (Σᵥ@ Σ α))])
            (cond [mut? (ret! (T->R V^ Φ^) Ξ Σ)]
                  [else (ret! ($@* Φ^ α) Ξ Σ)])
            )
          #:where
          [mut? (assignable? 𝒾)]
          [α (mk-α ((if (equal? lₒ l) -α:top -α:wrp) 𝒾))]
          [modify-V
           (ann (cond
                  [(equal? lₒ l) values]
                  [(symbol? l) (λ (V) (with-negative-party l V))]
                  [(λ ([V : V])
                     (with-positive-party 'dummy+
                       (with-negative-party l
                         (match V
                           [(X/G l³ C _) (X/G l³ C α•)]
                           [_ V]))))])
                (V → V))]]
      [=> (-@ E Es ℓ)
          (let ([Ρ₀ (m↓ Ρ fv₀)]
                [EΡs (for/list : (Listof EΡ) ([⟦E⟧ (in-list ⟦Es⟧)] [fv (in-list fvs)] [E (in-list Es)])
                       (EΡ ⟦E⟧ (m↓ Ρ fv)))])
            (⟦E⟧ (m↓ Ρ fv₀) Φ^ (K+ (F:Ap '() EΡs ℓ) Ξ) Σ))
          #:where ; HACK
          [_ (match* (E Es)
               [('scv:mon (cons (-b (? symbol? l)) _))
                (add-transparent-module! (symbol->string l))
                (add-transparent-module! (format "user-of-~a" l))]
               [(_ _) 'ignore])]
          [fv₀ (fv E)]
          [fvs (map fv Es)]
          [⟦E⟧ (↓/rn E)]
          [⟦Es⟧ (map ↓/rn Es)]]
      [=> (-if E E₁ E₂)
          (⟦E⟧ Ρ Φ^ (K+ (F:If l ⟦E₁⟧ ⟦E₂⟧ Ρ) Ξ) Σ)
          #:recur E E₁ E₂]
      [(-wcm Eₖ Eᵥ E) ???]
      [(-begin '()) (mk-T -void)]
      [(-begin (list E)) (↓ E)]
      [=> (-begin (cons E Es))
          (⟦E⟧ Ρ Φ^ (K+ (F:Bgn (assert ⟦Es⟧ pair?) Ρ) Ξ) Σ)
          #:recur E (Es ...)]
      [(-begin0 E₀ '()) (↓ E₀)]
      [=> (-begin0 E₀ Es)
          (⟦E₀⟧ Ρ Φ^ (K+ (F:Bgn0:V (assert ⟦Es⟧ pair?) Ρ) Ξ) Σ)
          #:recur E₀ (Es ...)]
      [(-quote (? Base? b)) (mk-T (-b b))]
      [(-quote q) ???]
      [(-let-values '() E _) (↓ E)]
      [=> (-let-values bnds E ℓ)
          (⟦E⟧ₓ Ρ Φ^ (K+ (F:Let ℓ x ⟦bnd⟧s '() ⟦E⟧ Ρ) Ξ) Σ)
          #:where [(cons (cons x ⟦E⟧ₓ) ⟦bnd⟧s) (map ↓-bnd bnds)]
          #:recur E]
      [(-letrec-values '() E _) (↓ E)]
      [=> (-letrec-values bnds E ℓ)
          (let ([Ρ* (init-undefined! Σ bnds (Ξ:co-ctx Ξ) Ρ)])
            (⟦E⟧ₓ Ρ* Φ^ (K+ (F:Letrec ℓ x ⟦bnd⟧s ⟦E⟧ Ρ*) Ξ) Σ))
          #:where [(cons (cons x ⟦E⟧ₓ) ⟦bnd⟧s) (map ↓-bnd bnds)]
          #:recur E]
      [=> (-set! x E)
          (⟦E⟧ Ρ Φ^ (K+ (F:Set! (get-addr Ρ)) Ξ) Σ)
          #:where [get-addr
                   (if (symbol? x)
                       (λ ([Ρ : Ρ]) (Ρ@ Ρ x))
                       (λ _ (mk-α (-α:top x))))]
          #:recur E]
      [(-error msg ℓ) (mk-Blm (Blm (strip-ℓ ℓ) 'Λ '(not-reached) (list (set (-b msg)))))]
      [=> (-μ/c x C)
          (⟦C⟧ (Ρ+ Ρ x (mk-α (-α:x/c x (Ξ:co-ctx Ξ)))) Φ^ (K+ (F:Μ/C x) Ξ) Σ)
          #:recur C]
      [(--> Cs D ℓ) (mk--> ℓ (-var-map ↓ Cs) (↓ D))]
      [(-->i Cs D) (mk-->i (map ↓-dom Cs) (↓-dom D))]
      [=> (-∀/c xs E*)
          (ret! (T->R (∀/C xs ⟦E*⟧ (m↓ Ρ fvs)) Φ^) Ξ Σ)
          #:where [fvs (fv E)]
          #:recur E*]
      [=> (-x/c x)
          (ret! (T->R (X/C (Ρ@ Ρ x)) Φ^) Ξ Σ)]
      [=> (-struct/c 𝒾 '() ℓ)
          (cond [(𝒾-defined? Σ) (ret! (R C Φ^) Ξ Σ)]
                [else (blm:undefined-struct 𝒾 ℓ)])
          #:where
          [𝒾-defined? (struct-defined? 𝒾)]
          [C (list {set (St/C #t 𝒾 '())})]]
      [=> (-struct/c 𝒾 (cons C Cs) ℓ)
          (cond [(𝒾-defined? Σ) (⟦C⟧ Ρ Φ^ (K+ (F:St/C ℓ 𝒾 '() ⟦Cs⟧ Ρ) Ξ) Σ)]
                [else (blm:undefined-struct 𝒾 ℓ)])
          #:where [𝒾-defined? (struct-defined? 𝒾)]
          #:recur C (Cs ...)]
      [_ (error '↓ₑ "unhandled: ~a" e)])
    
    (rn (↓ e) e)) 

  (define/memo (↓ₓ [x : Symbol] [ℓₓ : ℓ]) : ⟦E⟧
    (define blm:undefined (Blm (strip-ℓ ℓₓ) 'Λ '(defined?) (list {set -undefined})))
    (define mut? (assignable? x))
    (λ (Ρ Φ^ Ξ Σ)
      (define α (Ρ@ Ρ x))
      (define V^ (Σᵥ@ Σ α))
      (cond [(set-empty? V^) blm:undefined]
            [mut? (ret! (T->R V^ Φ^) Ξ Σ)]
            [else (ret! ($@* Φ^ α) Ξ Σ)])))

  (define (mk-T [T : (U T T^)]) : ⟦E⟧
    (mk-W (if (or (set? T) (S? T)) (list T) (list (set T)))))

  (define/memo (mk-W [W : W]) : ⟦E⟧
    (rn (λ (Ρ Φ^ Ξ Σ) (ret! (R W Φ^) Ξ Σ)) W))

  (define/memo (mk-Blm [blm : Blm]) : ⟦E⟧ (λ _ blm))

  (define/memo (mk-->i [⟦dom⟧s : (Listof ⟦dom⟧)] [⟦rng⟧ : ⟦dom⟧]) : ⟦E⟧
    (λ (Ρ Φ^ Ξ Σ)
      (define-values (Doms doms) (split-⟦dom⟧s Ρ (append ⟦dom⟧s (list ⟦rng⟧))))
      (match doms
        ['() (let ([G (==>i (reverse (cdr Doms)) (car Doms))])
               (ret! (T->R G Φ^) Ξ Σ))]
        [(cons (⟦dom⟧ x #f ⟦C⟧ ℓ) ⟦dom⟧s)
         (⟦C⟧ Ρ Φ^ (K+ (F:==>i Ρ Doms (cons x ℓ) ⟦dom⟧s) Ξ) Σ)])))

  (define/memo (mk--> [ℓ : ℓ] [⟦dom⟧s : (-var ⟦E⟧)] [⟦rng⟧ : ⟦E⟧]) : ⟦E⟧
    (match-define (-var ⟦C⟧s ⟦C⟧ᵣ) ⟦dom⟧s)
    (match ⟦C⟧s
      [(cons ⟦C⟧ ⟦C⟧s)
       (λ (Ρ Φ^ Ξ Σ) (⟦C⟧ Ρ Φ^ (K+ (F:==>:Dom '() ⟦C⟧s ⟦C⟧ᵣ ⟦rng⟧ Ρ ℓ) Ξ) Σ))]
      ['()
       (if ⟦C⟧ᵣ
           (λ (Ρ Φ^ Ξ Σ) (⟦C⟧ᵣ  Ρ Φ^ (K+ (F:==>:Rst '() ⟦rng⟧ Ρ ℓ) Ξ) Σ))
           (λ (Ρ Φ^ Ξ Σ) (⟦rng⟧ Ρ Φ^ (K+ (F:==>:Rng '() #f ℓ) Ξ) Σ)))]))

  (define/memo (mk-let* [ℓ : ℓ] [⟦bnd⟧s : (Assoc Symbol ⟦E⟧)] [⟦body⟧ : ⟦E⟧]) : ⟦E⟧
    (foldr
     (λ ([⟦bnd⟧ : (Pairof Symbol ⟦E⟧)] [⟦body⟧ : ⟦E⟧]) : ⟦E⟧
        (match-define (cons (app list x) ⟦E⟧ₓ) ⟦bnd⟧)
        (λ (Ρ Φ^ Ξ Σ)
          (⟦E⟧ₓ Ρ Φ^ (K+ (F:Let ℓ x '() '() ⟦body⟧ Ρ) Ξ) Σ)))
     ⟦body⟧
     ⟦bnd⟧s)) 

  (define/memo (mk-mon [ctx : Ctx] [⟦C⟧ : ⟦E⟧] [⟦V⟧ : ⟦E⟧]) : ⟦E⟧
    (λ (Ρ Φ^ Ξ Σ) (⟦C⟧ Ρ Φ^ (K+ (F:Mon:V ctx (EΡ ⟦V⟧ Ρ)) Ξ) Σ)))

  (define/memo (mk-app [ℓ : ℓ] [⟦f⟧ : ⟦E⟧] [⟦x⟧s : (Listof ⟦E⟧)]) : ⟦E⟧
    (λ (Ρ Φ^ Ξ Σ)
      (define EΡs : (Listof EΡ) (for/list ([⟦x⟧ (in-list ⟦x⟧s)]) (EΡ ⟦x⟧ Ρ)))
      (⟦f⟧ Ρ Φ^ (K+ (F:Ap '() EΡs ℓ) Ξ) Σ))) 

  (define/memo (mk-fc [ℓ : ℓ] [⟦C⟧ : ⟦E⟧] [⟦V⟧ : ⟦E⟧]) : ⟦E⟧
    (λ (Ρ Φ^ Ξ Σ) (⟦C⟧ Ρ Φ^ (K+ (F:Fc:V ℓ ⟦V⟧ Ρ) Ξ) Σ)))

  (define/memo (mk-wrapped [C : Prox/C] [ctx : Ctx] [α : α] [T : T^]) : ⟦E⟧
    (λ (ρ Φ^ Ξ Σ)
      (⊔T! Σ Φ^ α T)
      (ret! (T->R (X/G ctx C α) Φ^) Ξ Σ)))

  (: split-⟦dom⟧s : Ρ (Listof ⟦dom⟧) → (Values (Listof Dom) (Listof ⟦dom⟧)))
  (define (split-⟦dom⟧s Ρ ⟦dom⟧s)
    (let go ([Doms↓ : (Listof Dom) '()] [⟦dom⟧s : (Listof ⟦dom⟧) ⟦dom⟧s])
      (match ⟦dom⟧s
        ['() (values Doms↓ '())]
        [(cons (⟦dom⟧ x (? values xs) ⟦E⟧ ℓ) ⟦dom⟧s*)
         (go (cons (Dom x (Clo (-var xs #f) ⟦E⟧ Ρ) ℓ) Doms↓) ⟦dom⟧s*)]
        [_ (values Doms↓ ⟦dom⟧s)])))

  (: rn : ⟦E⟧ (U -e W -module -prog) → ⟦E⟧)
  ;; Just for debugging. Disable in production as renamed procedures are slower in tight loops
  (define (rn ⟦E⟧ x)
    #;⟦E⟧
    (let ([s (cond [(-e? x) (format "⟦~a⟧"(show-e x))]
                   [(-prog? x) (format "⟦~a⟧" (map show-module (-prog-_0 x)))]
                   [(-module? x) (format "⟦~a⟧" (show-module x))]
                   [else (format "⟦w ~a⟧" (map show-T x))])])
      (procedure-rename ⟦E⟧ (string->symbol s))))
  )
