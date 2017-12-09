#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (only-in racket/function curry)
         racket/set
         racket/bool
         racket/match
         racket/list
         typed/racket/unit
         racket/splicing
         syntax/parse/define
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(provide kont@)

(define-unit kont@
  (import compile^ app^ mon^ fc^ proof-system^ memoize^ for-gc^ verifier^ havoc^ meta-functions^
          val^ env^ sto^ pretty-print^ instr^ prim-runtime^ static-info^ path^
          sat-result^ unify^
          (prefix q: local-prover^))
  (export kont^)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Macros
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (splicing-let-syntax ([compute-frame-roots
                         (syntax-parser
                           [(_) #'∅eq]
                           [(_ root:id) #'(->⟪α⟫s root)]
                           [(_ root:id ...) #'(∪ (->⟪α⟫s root) ...)])])
    (define-simple-macro (make-frame (⟦k⟧:id A:id H:id φ:id Σ:id)
                           #:roots (root:id ...)
                           e ...)
      (let ([αₖ (⟦k⟧->αₖ ⟦k⟧)]
            [frame-roots (compute-frame-roots root ...)]
            [tail-roots (⟦k⟧->roots ⟦k⟧)])
        (define ⟦k⟧₀ (rt αₖ))
        (define ⟦k⟧* : -⟦k⟧
          (λ (A H φ Σ)
            (cond [(-blm? A) (⟦k⟧₀ A H φ Σ)]
                  [else e ...])))
        (set-⟦k⟧->αₖ! ⟦k⟧* αₖ)
        (add-⟦k⟧-roots! ⟦k⟧* (∪ frame-roots tail-roots))
        ⟦k⟧*)))

  (define-simple-macro (define-frame (φ:id [arg:id (~literal :) τ] ...) e ...)
    (define/memo (φ [arg : τ] ...) : -⟦k⟧ e ...))

  (splicing-local
      ((define print-cache : (HashTable -blm Void) (make-hash)))

    ;; Base continuation that returns locally finished configuration
    (define-frame (rt [αₖ : -αₖ])
      (define ⟦k⟧ : -⟦k⟧
        (λ (A H φ Σ)
          (define (maybe-print-blame)
            (when (and (debug-iter?) (-blm? A))
              (hash-ref! print-cache A
                         (λ ()
                           (printf "~a~n" (show-A A))
                           #;(begin
                             (printf "context:~n")
                             (for ([e (-H->-ℋ H)])
                               (printf "- ~a~n" (show-edge e)))
                             (printf "cache: ~n")
                             (for ([(l t) $])
                               (printf "- ~a ↦ ~a~n" (show-loc l) (show-t t)))
                             (printf "pc: ~a~n" (show-Γ Γ))
                             (error 'first-blame))))))
          (match A
            [(-blm l+ _ _ _ _) #:when (not (transparent-module? l+)) ∅]
            [_
             (maybe-print-blame)
             (if (-blm? A)
                 {set (-ς! αₖ A)}
                 {set (-ς↓ αₖ A φ)})])))
      (set-⟦k⟧->αₖ! ⟦k⟧ αₖ)
      (add-⟦k⟧-roots! ⟦k⟧ ∅eq)
      ⟦k⟧))

  (define-frame (ap∷ [Vs : (Listof -V^)]
                     [⟦e⟧s : (Listof -⟦e⟧)]
                     [ρ₀ : -ρ]
                     [ℓ : ℓ]
                     [⟦k⟧ : -⟦k⟧])
    (define ρ (m↓ ρ₀ (apply ∪ ∅eq (map fv-⟦e⟧ ⟦e⟧s))))
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vs ρ)
      (match A
        [(list V)
         (define Vs* (cons V Vs))
         (match ⟦e⟧s
           ['()
            (match-define (cons Vₕ Vₓs) (reverse Vs*))
            (app ℓ Vₕ Vₓs H φ Σ ⟦k⟧)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (⟦e⟧ ρ H φ Σ (ap∷ Vs* ⟦e⟧s* ρ ℓ ⟦k⟧))])]
        [_
         (define l (ℓ-src ℓ))
         (define blm
           (blm/simp l 'Λ (list '1-value) (list {set (format-symbol "~a values" (length Vs))}) ℓ))
         (⟦k⟧ blm H φ Σ)])))

  (define-frame (mon.c∷ [ctx : -ctx] [C : (U (Pairof -⟦e⟧ -ρ) -V^)] [⟦k⟧ : -⟦k⟧])
    (match-define (-ctx _ _ lo ℓ) ctx)
    (define root (if (pair? C) (cdr C) C))
    (make-frame (⟦k⟧ A H φ Σ) #:roots (root)
      (match A
        [(list V)
         (cond [(set? C) (push-mon ctx C V H φ Σ ⟦k⟧)]
               [else
                (match-define (cons ⟦c⟧ ρ) C)
                (⟦c⟧ ρ H φ Σ (mon.v∷ ctx V ⟦k⟧))])]
        [else
         (define blm (blm/simp lo 'Λ (list {set '|1 value|}) A ℓ))
         (⟦k⟧ blm H φ Σ)])))

  (define-frame (mon.v∷ [ctx : -ctx] [V : (U (Pairof -⟦e⟧ -ρ) -V^)] [⟦k⟧ : -⟦k⟧])
    (match-define (-ctx _ _ lo ℓ) ctx)
    (define root (if (pair? V) (cdr V) V))
    (make-frame (⟦k⟧ A H φ Σ) #:roots (root)
      (match A
        [(list C)
         (cond [(set? V) (push-mon ctx C V H φ Σ ⟦k⟧)]
               [else
                (match-define (cons ⟦v⟧ ρ) V)
                (⟦v⟧ ρ H φ Σ (mon.c∷ ctx C ⟦k⟧))])]
        [else
         (define blm (blm/simp lo 'Λ '(|1 value|) A ℓ))
         (⟦k⟧ blm H φ Σ)])))

  (define-frame (mon*.c∷ [ctx : -ctx] [rngs : (U (Listof -⟪α⟫ℓ) 'any)] [⟦k⟧ : -⟦k⟧])
    (case rngs
      [(any) ⟦k⟧]
      [else
       (define-values (βs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc rngs))
       (define n (length rngs))
       (match-define (-ctx l+ _ lo ℓ) ctx)
       (make-frame (⟦k⟧ A H φ Σ) #:roots (βs)
         (cond
           [(= n (length A))
            (match* ((σ@/list Σ (-φ-cache φ) βs) A ℓs)
              [((cons C₁ Cs) (cons V₁ Vs) (cons ℓ₁ ℓs))
               (push-mon (ctx-with-ℓ ctx ℓ₁) C₁ V₁ H φ Σ (mon*∷ ctx Cs Vs ℓs '() ⟦k⟧))]
              [('() '() '())
               (⟦k⟧ '() H φ Σ)])]
           [else
            (define msg
              (format-symbol (case n
                               [(0 1) "~a value"]
                               [else "~a values"])
                             n))
            (define blm (blm/simp l+ lo (list msg) A ℓ))
            (⟦k⟧ blm H φ Σ)]))]))

  (define-frame (mon*∷ [ctx : -ctx]
                       [Cs : (Listof -V^)]
                       [Vs : (Listof -V^)]
                       [ℓs : (Listof ℓ)]
                       [res.rev : (Listof -V^)]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Cs Vs)
      (match-define (list V) A)
      (define res.rev* (cons V res.rev))
      (match* (Cs Vs ℓs)
        [((cons C₁ Cs*) (cons V₁ Vs*) (cons ℓ₁ ℓs*))
         (push-mon (ctx-with-ℓ ctx ℓ₁) C₁ V₁ H φ Σ (mon*∷ ctx Cs* Vs* ℓs* res.rev* ⟦k⟧))]
        [('() '() '())
         (⟦k⟧ (reverse res.rev*) H φ Σ)])))

  ;; let-values
  (define-frame (let∷ [ℓ : ℓ]
                      [xs : (Listof Symbol)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                      [bnd-Vs : (Listof (Pairof Symbol -V^))]
                      [⟦e⟧ : -⟦e⟧]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧])
    (define n (length xs))
    (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
      (cond
        [(= (length A) n)
         (define bnd-Vs*
           (for/fold ([acc : (Listof (Pairof Symbol -V^)) bnd-Vs])
                     ([x (in-list xs)] [V (in-list A)])
             (cons (cons x V) acc)))
         (match ⟦bnd⟧s
           ['()
            (define-values (ρ* φ*)
              (let-values ([(xs Vs) (unzip bnd-Vs*)])
                (bind-args Σ ρ ℓ H φ xs Vs)))
            (⟦e⟧ ρ* H φ* Σ ⟦k⟧)]
           [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
            (⟦e⟧* ρ H φ Σ (let∷ ℓ xs* ⟦bnd⟧s* bnd-Vs* ⟦e⟧ ρ ⟦k⟧))])]
        [else
         (define blm
           (blm/simp (ℓ-src ℓ) 'let-values
                     (list (format-symbol "requires ~a values" n))
                     (list {set (format-symbol "provided ~a values" (length A))})
                     +ℓ₀))
         (⟦k⟧ blm H φ Σ)])))

  ;; begin
  (define-frame (bgn∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
         (⟦e⟧ ρ H φ Σ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))

  ;; begin0, waiting on first value
  (define-frame (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
         (⟦e⟧ ρ H φ Σ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

  ;; begin0, already have first value
  (define-frame (bgn0.e∷ [A : (Listof -V^)] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['()
       (make-frame (⟦k⟧ _ H φ Σ) #:roots (A)
         (⟦k⟧ A H φ Σ))]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (make-frame (⟦k⟧ _ H φ Σ) #:roots (A ρ)
         (⟦e⟧ ρ H φ Σ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

  ;; Conditional
  (define-frame (if∷ [l : -l] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
      (match A
        [(list V^)
         (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ (-Σ-σ Σ) φ 'values V^)]) : -ς
           #:true  (⟦e⟧₁ ρ H φ₁ Σ ⟦k⟧)
           #:false (⟦e⟧₂ ρ H φ₂ Σ ⟦k⟧))]
        [_
         (define msg (format-symbol "~a values" (length A)))
         (⟦k⟧ (blm/simp l 'Λ '(1-value) (list {set msg}) +ℓ₀) H φ Σ)])))

  ;; set!
  (define-frame (set!∷ [α : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (match A
        [(list V)
         (⟦k⟧ (list {set -void}) H (mut! Σ φ α V) Σ)]
        [_
         (define msg (format-symbol "~a values" (length A)))
         (define blm (blm/simp 'TODO 'Λ (list '1-value) (list {set msg}) +ℓ₀))
         (⟦k⟧ blm H φ Σ)])))

  ;; letrec-values
  (define-frame (letrec∷ [ℓ : ℓ]
                         [xs : (Listof Symbol)]
                         [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                         [⟦e⟧ : -⟦e⟧]
                         [ρ : -ρ]
                         [⟦k⟧ : -⟦k⟧])
    (define n (length xs))
    (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
      (cond
        [(= n (length A))
         (define αs : (Listof ⟪α⟫) (for/list ([x (in-list xs)]) (ρ@ ρ x)))
         (define φ* (mut*! Σ φ αs A))
         (match ⟦bnd⟧s
           ['()
            (⟦e⟧ ρ H φ* Σ ⟦k⟧)]
           [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
            (⟦e⟧* ρ H φ* Σ (letrec∷ ℓ xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))])]
        [else
         (define blm
           (blm/simp (ℓ-src ℓ) 'letrec-values
                 (list (format-symbol "~a values" n))
                 (list {set (format-symbol "~a values" (length A))})
                 +ℓ₀))
         (⟦k⟧ blm H φ Σ)])))

  ;; μ/c
  (define-frame (μ/c∷ [x : Symbol] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (match-define (list V) A)
      (define α (-α->⟪α⟫ (-α.x/c x H)))
      (⟦k⟧ (list {set (-x/C α)}) H (alloc Σ φ α V) Σ)))

  ;; Non-dependent contract domain
  (define-frame (-->.dom∷ [Vs  : (Listof -V^)]
                          [⟦c⟧s : (Listof -⟦e⟧)]
                          [⟦c⟧ᵣ : (Option -⟦e⟧)]
                          [⟦d⟧  : -⟦e⟧]
                          [ρ   : -ρ]
                          [ℓ   : ℓ]
                          [⟦k⟧  : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vs ρ)
      (match-define (list V) A)
      (define Vs* (cons V Vs))
      (match ⟦c⟧s
        ['()
         (cond [⟦c⟧ᵣ  (⟦c⟧ᵣ ρ H φ Σ (-->.rst∷ Vs* ⟦d⟧ ρ ℓ ⟦k⟧))]
               [else (⟦d⟧ ρ H φ Σ (-->.rng∷ Vs* #f ℓ ⟦k⟧))])]
        [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ ρ H φ Σ (-->.dom∷ Vs* ⟦c⟧s* ⟦c⟧ᵣ ⟦d⟧ ρ ℓ ⟦k⟧))])))

  ;; Non-depenent contract rest
  (define-frame (-->.rst∷ [Vs : (Listof -V^)]
                          [⟦d⟧ : -⟦e⟧]
                          [ρ : -ρ]
                          [ℓ : ℓ]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vs ρ)
      (match-define (list Vᵣ) A)
      (⟦d⟧ ρ H φ Σ (-->.rng∷ Vs Vᵣ ℓ ⟦k⟧))))

  ;; Non-dependent contract range
  (define-frame (-->.rng∷ [Vs : (Listof -V^)]
                          [Vᵣ : (Option -V^)]
                          [ℓ : ℓ]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vs)
      (define-values (C φ*) (mk-=> Σ H φ Vs Vᵣ A ℓ))
      (⟦k⟧ (list {set C}) H φ* Σ)))

  (splicing-local
      ()

    (: mk-=> : -Σ -H -φ (Listof -V^) (Option -V^) (Listof -V^) ℓ → (Values -V -φ))
    (define (mk-=> Σ H φ doms.rev rst rngs ℓ) 
      (define-values (Dom φ₁)
        (let-values ([(Init φ*) (mk-⟪α⟫ℓ* Σ 'dom -α.dom H ℓ φ (reverse doms.rev))])
          (cond [rst (define αᵣ (-α->⟪α⟫ (-α.rst ℓ H)))
                     (define ℓᵣ (ℓ-with-id ℓ 'rest))
                     (values (-var Init (-⟪α⟫ℓ αᵣ ℓᵣ)) (alloc Σ φ* αᵣ rst))]
                [else (values Init φ*)])))
      (define-values (Rng φ₂)
        (match rngs
          ['(any) (values 'any φ₁)]
          [_ (mk-⟪α⟫ℓ* Σ 'rng -α.rng H ℓ φ₁ rngs)]))
      (values (-=> Dom Rng) φ₂))

    ;; Given *reversed* list of contract domains and range-maker, create dependent contract
    (: mk-=>i : -Σ -H -φ (Listof -V^) -Clo ℓ → (Values -V -φ))
    (define (mk-=>i Σ H φ Vs-rev Mk-D ℓₐ)
      (define-values (Dom φ*) (mk-⟪α⟫ℓ* Σ 'dom -α.dom H ℓₐ φ (reverse Vs-rev)))
      (values (-=>i Dom (cons Mk-D (ℓ-with-id ℓₐ '->i-rng))) φ*))) 

  ;; Dependent contract
  (define-frame (-->i∷ [Cs  : (Listof -V^)]
                       [⟦c⟧s : (Listof -⟦e⟧)]
                       [ρ   : -ρ]
                       [Mk-D : -Clo]
                       [ℓ    : ℓ]
                       [⟦k⟧  : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Cs ρ Mk-D)
      (match-define (list C) A)
      (define Cs* (cons C Cs))
      (match ⟦c⟧s
        ['()
         (define-values (G φ*) (mk-=>i Σ H φ Cs* Mk-D ℓ))
         (⟦k⟧ (list {set G}) H φ* Σ)]
        [(cons ⟦c⟧ ⟦c⟧s*)
         (⟦c⟧ ρ H φ Σ (-->i∷ Cs* ⟦c⟧s* ρ Mk-D ℓ ⟦k⟧))])))

  ;; struct/c contract
  (define-frame (struct/c∷ [ℓ₁ : ℓ]
                           [𝒾 : -𝒾]
                           [Cs : (Listof -V^)]
                           [⟦c⟧s : (Listof -⟦e⟧)]
                           [ρ : -ρ]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (#;Cs ρ)
      (match-define (list C) A)
      (define Cs* (cons C Cs))
      (match ⟦c⟧s
        ['()
         (define-values (Fields φ*) (mk-⟪α⟫ℓ* Σ (-𝒾-name 𝒾) (curry -α.struct/c 𝒾) H ℓ₁ φ (reverse Cs*)))
         (define flat? (andmap C^-flat? Cs*))
         (define StC (-St/C flat? 𝒾 Fields))
         (⟦k⟧ (list {set StC}) H φ* Σ)]
        [(cons ⟦c⟧ ⟦c⟧s*)
         (⟦c⟧ ρ H φ Σ (struct/c∷ ℓ₁ 𝒾 Cs* ⟦c⟧s* ρ ⟦k⟧))])))

  ;; define
  (define-frame (def∷ [l : -l]
                  [αs : (Listof ⟪α⟫)]
                  [⟦k⟧ : -⟦k⟧])
    (define n (length αs))
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (cond
        [(= n (length A))
         (⟦k⟧ (list {set -void}) H (alloc* Σ φ αs A) Σ)]
        [else
         (define blm
           (blm/simp l 'define-values
                 (list (format-symbol "~a values" n))
                 (list {set (format-symbol "~a values" (length A))})
                 +ℓ₀))
         (⟦k⟧ blm H φ Σ)])))

  ;; provide with contract
  (define-frame (dec∷ [ℓ : ℓ] [𝒾 : -𝒾] [⟦k⟧ : -⟦k⟧])
    (define l (-𝒾-src 𝒾))
    (define ctx (-ctx l 'dummy- l ℓ))
    (define α (-α->⟪α⟫ 𝒾))
    (define α* (-α->⟪α⟫ (-α.wrp 𝒾)))
    (make-frame (⟦k⟧ A H φ Σ) #:roots (α)
      (match-define (list C) A)
      (define Vs (σ@ Σ (-φ-cache φ) α))
      (push-mon ctx C Vs H φ Σ (def∷ l (list α*) ⟦k⟧))))

  (define/memo (hv∷ [tag : HV-Tag] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define φ* (add-leak! tag Σ φ A))
      {set (-ς↑ (σₖ+! Σ (-αₖ H (-HV tag) φ*) ⟦k⟧))}))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Helper frames
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-frame (mk-wrap-vect∷ [Vₚ : (U -Vector/C -Vectorof)]
                               [ctx : -ctx]
                               [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vₚ)
      (match-define (list Vᵥ) A) ; only used internally, shoule be safe
      (define αᵥ (-α->⟪α⟫ (-α.unvct ctx H)))
      (⟦k⟧ (list {set (-Vector/guard Vₚ αᵥ ctx)}) H (alloc Σ φ αᵥ Vᵥ) Σ)))

  (define-frame (mon-or/c∷ [ctx : -ctx] [Cₗ : -V^] [Cᵣ : -V^] [V : -V^] [⟦k⟧ : -⟦k⟧])
  (make-frame (⟦k⟧ A H φ Σ) #:roots (Cₗ Cᵣ V)
    (match A
      [(list _)
       (push-mon ctx Cᵣ V H φ Σ ⟦k⟧)]
      [(list _ V)
       (define Vₐ (for/union : -V^ ([C (in-set Cₗ)])
                     (V+ (-Σ-σ Σ) φ V C)))
       (⟦k⟧ (list Vₐ) H φ Σ)])))

  (define-frame (if.flat/c∷ [V* : -V^] [blm : -blm] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (V*)
      (match A
        [(list V^)
         (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ (-Σ-σ Σ) φ 'values V^)]) : -ς
           #:true  (⟦k⟧ (list V*) H φ₁ Σ)
           #:false (⟦k⟧ blm       H φ₂ Σ))]
        [_
         (match-define (-blm _ lo _ _ ℓ) blm)
         (⟦k⟧ (blm/simp lo 'Λ '(|1 value|) A ℓ) H φ Σ)])))

  (define-frame (wrap-st∷ [C : -St/C] [ctx : -ctx] [⟦k⟧ : -⟦k⟧])
  (make-frame (⟦k⟧ A H φ Σ) #:roots (C)
    (match-define (list V) A)  ; only used internally, should be safe
    (define αᵤ (-α->⟪α⟫ (-α.st (-St/C-id C) ctx H)))
    (⟦k⟧ (list {set (-St* C αᵤ ctx)}) H (alloc Σ φ αᵤ V) Σ)))

  (define-frame (fc-and/c∷ [l : -l]
                           [ℓ : ℓ]
                           [C₁ : -V^]
                           [C₂ : -V^]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C₁ C₂)
      (match A
        [(list _) (⟦k⟧ (list {set -ff}) H φ Σ)]
        [(list _ V)
         (define Vₐ (for/union : -V^ ([C (in-set C₁)])
                       (V+ (-Σ-σ Σ) φ V C)))
         (push-fc l ℓ C₂ Vₐ H φ Σ ⟦k⟧)])))

  (define-frame (fc-or/c∷ [l : -l]
                          [ℓ : ℓ]
                          [C₁ : -V^]
                          [C₂ : -V^]
                          [V : -V^]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C₁ C₂)
      (match A
        [(list _)
         (push-fc l ℓ C₂ V H φ Σ ⟦k⟧)]
        [(list _ V)
         (define Vₐ (for/union : -V^ ([C (in-set C₁)]) (V+ (-Σ-σ Σ) φ V C)))
         (⟦k⟧ (list {set -tt} Vₐ) H φ Σ)])))

  (define-frame (fc-not/c∷ [V^ : -V^] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (V^)
      (match A
        [(list _)
         (⟦k⟧ (list {set -tt} V^) H φ Σ)]
        [(list _ _)
         (⟦k⟧ (list {set -ff}) H φ Σ)])))

  (define-frame (fc-struct/c∷ [l : -l]
                              [ℓ : ℓ]
                              [𝒾 : -𝒾]
                              [Vs-rev : (Listof -V^)]
                              [⟦e⟧s : (Listof -⟦e⟧)]
                              [ρ : -ρ]
                              [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vs-rev ρ)
      (match A
        [(list _)
         (⟦k⟧ (list {set -ff}) H φ Σ)]
        [(list _ V*)
         (match ⟦e⟧s
           ['()
            (define ⟦k⟧*
              (let ([k (-st-mk 𝒾)])
                (ap∷ (append Vs-rev (list {set k})) '() ⊥ρ ℓ
                     (ap∷ (list {set -tt} {set 'values}) '() ⊥ρ ℓ ⟦k⟧))))
            (⟦k⟧* (list V*) H φ Σ)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (⟦e⟧ ρ H φ Σ (fc-struct/c∷ l ℓ 𝒾 (cons V* Vs-rev) ⟦e⟧s* ρ ⟦k⟧))])])))

  (define-frame (fc.v∷ [l : -l]
                       [ℓ : ℓ]
                       [⟦v⟧ : -⟦e⟧]
                       [ρ : -ρ]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
      (match A
        [(list C)
         (⟦v⟧ ρ H φ Σ (fc.c∷ l ℓ C ⟦k⟧))]
        [_
         (⟦k⟧ (blm/simp l 'Λ '(|1 value|) A ℓ) H φ Σ)])))

  (define-frame (fc.c∷ [l : -l]
                       [ℓ : ℓ]
                       [C : -V^]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C)
      (match A
        [(list V)
         (push-fc l ℓ C V H φ Σ ⟦k⟧)]
        [_
         (define blm (blm/simp l 'Λ '(|1 value|) A ℓ))
         (⟦k⟧ blm H φ Σ)])))

  (define (and∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (if∷ l ⟦e⟧ (mk-V -ff) ρ (and∷ l ⟦e⟧s* ρ ⟦k⟧))]))

  (define (or∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*) ; TODO propagate value instead
       (if∷ l (mk-V -tt) ⟦e⟧ ρ (or∷ l ⟦e⟧s* ρ ⟦k⟧))]))

  (define-frame (restore-ctx∷ [H : -H] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A _ φ Σ) #:roots ()
      (⟦k⟧ A H φ Σ)))

  (define-frame (hash-set-inner∷ [ℓ : ℓ] [αₕ : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (αₕ)
      (match-define (list Vₖ Vᵥ) A)
      (app ℓ {set 'hash-set} (list (σ@ Σ (-φ-cache φ) αₕ) Vₖ Vᵥ) H φ Σ ⟦k⟧)))

  (define-frame (wrap-hash∷ [C : -Hash/C] [ctx : -ctx] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C)
      (match-define (list Vₕ) A)
      (define α (-α->⟪α⟫ (-α.unhsh ctx H)))
      (define Vₐ (-Hash/guard C α ctx))
      (⟦k⟧ (list {set Vₐ}) H (alloc Σ φ α Vₕ) Σ)))

  (define-frame (set-add-inner∷ [ℓ : ℓ] [αₛ : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (αₛ)
      (match-define (list Vₑ) A)
      (define Vₛ (σ@ Σ (-φ-cache φ) αₛ))
      (app ℓ {set 'set-add} (list Vₛ Vₑ) H φ Σ ⟦k⟧)))

  (define-frame (wrap-set∷ [C : -Set/C] [ctx : -ctx] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C)
      (match-define (list Vₛ) A)
      (define α (-α->⟪α⟫ (-α.unset ctx H)))
      (define Vₐ (-Set/guard C α ctx))
      (⟦k⟧ (list {set Vₐ}) H (alloc Σ φ α Vₛ) Σ)))

  (define-frame (maybe-havoc-prim-args∷ [ℓ : ℓ] [o : Symbol] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define σ (-Σ-σ Σ))
      (define behavioral-args
        (for*/set: : -V^ ([V^ (in-list A)]
                          [V (in-set V^)]
                          #:when (behavioral? σ (-φ-cache φ) V))
          V))
      (if (set-empty? behavioral-args)
          (⟦k⟧ A H φ Σ)
          (app (ℓ-with-id ℓ 'prim-havoc)
               {set (-Fn● 1 (cons o H))}
               (list behavioral-args)
               H φ Σ
               (bgn0.e∷ A '() ⊥ρ ⟦k⟧)))))

  (define-frame (make-prim-range∷ [ctx : -ctx]
                                  [?rng-wrap : (Option (Listof -⟪α⟫ℓ))]
                                  [ranges : (Listof -V^)]
                                  [cases : (Listof (List (Listof -V) (Option -V) (Listof -V)))]
                                  [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define refined-ranges (maybe-refine ranges (-Σ-σ Σ) φ cases A))
      (define ⟦k⟧* (if ?rng-wrap (mon*.c∷ ctx ?rng-wrap ⟦k⟧) ⟦k⟧))
      (⟦k⟧* refined-ranges H φ Σ)))

  (define-frame (implement-predicate∷ [o : Symbol] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (⟦k⟧ (list (implement-predicate (-Σ-σ Σ) φ o A)) H φ Σ)))

  (define-frame (absurd∷ [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
       ∅))

  (define-frame (rename∷ [m : (HashTable -t -t)] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
       (define Vs : (Listof -V^)
         (for/list ([V^ (in-list A)])
           (rename-V^ m V^)))
       (⟦k⟧ Vs H φ Σ)))

  (: σₖ+! : -Σ -αₖ -⟦k⟧ → -αₖ)
  (define (σₖ+! Σ αₖ ⟦k⟧)
    (define Ξ  (-Σ-Ξ Σ))
    (define σₖ (-Σ-σₖ Σ))
    (match-define (-αₖ H Bl φ) αₖ)
    (define-values (Ξ* ⟦k⟧* αₖ*)
      (match (recall Ξ αₖ)
        [(cons αₖ₀ m)
         (values Ξ (rename∷ (Bij-bw m) ⟦k⟧) αₖ₀)]
        [#f
         (define αₖ* (gc-αₖ Σ αₖ ⟦k⟧))
         (values (hash-update Ξ H (λ ([ctxs : (Listof -αₖ)]) (cons αₖ* ctxs)) (λ () '()))
                 ⟦k⟧
                 αₖ*)]))
    (define σₖ* (hash-update σₖ αₖ* (λ ([⟦k⟧s : (℘ -⟦k⟧)]) (set-add ⟦k⟧s ⟦k⟧*)) mk-∅))
    (set--Σ-σₖ! Σ σₖ*)
    (set--Σ-Ξ!  Σ Ξ* )
    αₖ*)
  
  (: maybe-refine : (Listof -V^) -σ -φ (Listof (List (Listof -V) (Option -V) (Listof -V))) (Listof -V^) → (Listof -V^))
  (define (maybe-refine rng₀ σ φ cases args)

    (: ⊢/quick : -V -V^ → -R)
    (define (⊢/quick o V^)
      (match o
        [(-Not/C (-⟪α⟫ℓ (app ⟪α⟫->-α (-α.imm C)) _)) (not-R (⊢/quick C V^))]
        [(? -h? p)                                   (q:p∋V^ σ φ p V^)]
        [_ '?]))

    (for/fold ([rng : (Listof -V^) rng₀])
              ([kase (in-list cases)])
      (match-define (list dom-inits ?dom-rst refinements) kase)
      (: check-inits : (Listof -V) (Listof -V^) → (Listof -V^))
      (define (check-inits doms args)
        (match* (doms args)
          [((cons dom doms*) (cons arg args*))
           (case (⊢/quick dom arg)
             [(✓) (check-inits doms* args*)]
             [else rng])]
          [('() _) (check-rest args)]
          [((cons _ _) '()) rng]))
      (: check-rest : (Listof -V^) → (Listof -V^))
      (define (check-rest args)
        (cond
          [?dom-rst
           (let go : (Listof -V^) ([args : (Listof -V^) args])
            (match args
              ['() (refine-rng)]
              [(cons arg args*)
               (case (⊢/quick ?dom-rst arg)
                 [(✓) (go args*)]
                 [else rng])]))]
          [else (if (null? args) (refine-rng) rng)]))
      (define (refine-rng)
        (for/list : (Listof -V^) ([rngᵢ (in-list rng)]
                                  [refᵢ (in-list refinements)])
          (V+ σ φ rngᵢ refᵢ)))
      (check-inits dom-inits args)))

  (: mk-⟪α⟫ℓ* : -Σ Symbol (ℓ -H Index → -α) -H ℓ -φ (Listof -V^) → (Values (Listof -⟪α⟫ℓ) -φ))
  (define (mk-⟪α⟫ℓ* Σ tag mk-α H ℓ φ Vs)
    (define-values (αℓs φ*)
      (for/fold ([αℓs-rev : (Listof -⟪α⟫ℓ) '()] [φ : -φ φ])
                ([V (in-list Vs)] [i (in-naturals)] #:when (index? i))
        (define α (-α->⟪α⟫ (mk-α ℓ H i)))
        (define αℓ (-⟪α⟫ℓ α (ℓ-with-id ℓ (cons tag i))))
        (values (cons αℓ αℓs-rev) (alloc Σ φ α V))))
    (values (reverse αℓs) φ*))

  (: recall : -Ξ -αₖ → (Option (Pairof -αₖ Uni)))
  (define (recall Ξ αₖ)
    (match-define (-αₖ H Bl φ) αₖ)

    (: search : (Listof -αₖ) → (Option (Pairof -αₖ Uni)))
    (define (search ctxs)
      (match ctxs
        [(cons (and αₖ₀ (-αₖ (== H) Bl₀ φ₀)) ctxs*)
         (match (unify-Bl Bl Bl₀)
           [(? values m)
            (if (φ⊑/m? m φ φ₀) (cons αₖ₀ m) (search ctxs*))]
           [#f (search ctxs*)])]
        ['() #f]))
    
    (cond
      [(hash-ref Ξ H #f) => search]
      [else #f]))

  (define/memoeq (fv-⟦e⟧ [⟦e⟧ : -⟦e⟧]) : (℘ Symbol)
    (cond [(recall-e ⟦e⟧) => fv]
          [else (error 'fv-⟦e⟧ "nothing")]))
  )
