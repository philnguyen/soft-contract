#lang typed/racket/base

;; Each function `↝._` implements semantics of corresponding continuation frame,
;; returning ⟦e⟧→⟦e⟧.
;; This is factored out because it's used in both compilation `⇓` and resumption `ℰ⟦_⟧`.

(provide (all-defined-out)
         (all-from-out "continuation-if.rkt")
         (all-from-out "continuation-amb.rkt")
         (all-from-out "ap.rkt")
         (all-from-out "continuation-begin.rkt"))

(require racket/match
         racket/set
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "helpers.rkt"
         "continuation-if.rkt"
         "continuation-amb.rkt"
         "continuation-begin.rkt"
         "ap.rkt")

(: ↝.def : Mon-Party (Listof (U -α.def -α.wrp)) → -⟦ℰ⟧)
;; Define top-level `xs` to be values from `⟦e⟧`
(define ((↝.def l αs) ⟦e⟧)
  (define (ℰ+ [ℰ : -ℰ]) (-ℰ.def l αs ℰ))
  (define (kont [σ : -σ] [Γ : -Γ] [X : -ΔX] [W : -W])
    (define Vs (-W-Vs W))
    (with-guarded-arity (length αs) (l Γ Vs)
      (define δσ
        (for/fold ([δσ : -Δσ ⊥σ]) ([α αs] [V Vs])
          (⊔ δσ α V)))
      (values δσ {set (-ΓW Γ -Void/W)} ∅ ∅ ∅)))
  (λ (M σ X ℒ)
    (apply/values (acc σ X ℰ+ kont) (⟦e⟧ M σ X ℒ))))

(: ↝.dec : -𝒾 -ℓ → -⟦ℰ⟧)
;; Make `⟦c⟧`. the contract for `𝒾`.
(define ((↝.dec 𝒾 ℓ) ⟦c⟧)
  (define (ℰ+ [ℰ : -ℰ]) (-ℰ.dec 𝒾 ℰ ℓ))
  (define l (-𝒾-ctx 𝒾))
  (define ⟦ℰ⟧-wrp (↝.def l (list (-α.wrp 𝒾))))
  (define l³ (Mon-Info l 'dummy l))
  (λ (M σ X ℒ)
    (apply/values
     (acc
      σ
      X
      ℰ+
      (λ (σ* Γ* X* W)
        (match-define (-W Vs c) W)
        (with-guarded-arity 1 (l Γ* Vs)
          (match-define (list C) Vs)
          (define ℒ* (-ℒ-with-Γ ℒ Γ*))
          (define W-C (-W¹ C c))
          (for*/ans ([V (σ@ σ (-α.def 𝒾))])
            ((⟦ℰ⟧-wrp (mon l³ ℓ W-C (-W¹ V 𝒾))) M σ* X* ℒ*)))))
     (⟦c⟧ M σ X ℒ))))

(: ↝.set! : Var-Name → -⟦ℰ⟧)
(define ((↝.set! x) ⟦e⟧)
  (define (ℰ+ [ℰ : -ℰ]) (-ℰ.set! x ℰ))
  (λ (M σ X ℒ)
    (apply/values
     (acc
      σ
      X
      ℰ+
      (λ (σ* Γ* X* W)
        (match-define (-W Vs s) W)
        (with-guarded-arity 1 ('TODO Γ* Vs)
          (match-define (list V) Vs)
          (define α (ρ@ (-ℒ-env ℒ) x))
          (values (⊔ ⊥σ α V) {set (-ΓW Γ* -Void/W)} ∅ {set α} ∅))))
     (⟦e⟧ M σ X ℒ))))

(: ↝.μ/c : Mon-Party -ℓ → -⟦ℰ⟧)
(define ((↝.μ/c l x) ⟦c⟧)
  (define (ℰ+ [ℰ : -ℰ]) (-ℰ.μ/c l x ℰ))
  (λ (M σ X ℒ)
    (apply/values
     (acc
      σ
      X
      ℰ+
      (λ (σ* Γ* X* W)
        (match-define (-W Vs v) W)
        (with-guarded-arity 1 (l Γ* Vs)
          (match-define (list V) Vs)
          (values (⊔ ⊥σ (-α.x/c x) V) {set (-ΓW Γ* W)} ∅ ∅ ∅))))
     (⟦c⟧ M σ X ℒ))))

(: ↝.-->.dom : Mon-Party (Listof -W¹) (Listof -⟦e⟧) -⟦e⟧ -ℓ → -⟦ℰ⟧)
(define ((↝.-->.dom l Ws ⟦c⟧s ⟦d⟧ ℓ) ⟦c⟧)
  (λ (M σ X ℒ)
    (apply/values
     (acc
      σ
      X
      (λ (ℰ) (-ℰ.-->.dom l Ws ℰ ⟦c⟧s ⟦d⟧ ℓ))
      (λ (σ* Γ* X* W)
        (match-define (-W Vs s) W)
        (with-guarded-arity 1 (l Γ* Vs)
          (match-define (list V) Vs)
          (define Ws* (cons (-W¹ V s) Ws))
          (define ℒ* (-ℒ-with-Γ ℒ Γ*))
          (match ⟦c⟧s
            ['()             (((↝.-->.rng l Ws* ℓ) ⟦d⟧) M σ* X* ℒ*)]
            [(cons ⟦c⟧* ⟦c⟧s*) (((↝.-->.dom l Ws* ⟦c⟧s* ⟦d⟧ ℓ) ⟦c⟧*) M σ* X* ℒ*)]))))
     (⟦c⟧ M σ X ℒ))))

(: ↝.-->.rng : Mon-Party (Listof -W¹) -ℓ → -⟦ℰ⟧)
(define ((↝.-->.rng l Ws ℓ) ⟦d⟧)
  (λ (M σ X ℒ)
    (apply/values
     (acc
      σ
      X
      (λ (ℰ) (-ℰ.-->.rng l Ws ℰ ℓ))
      (λ (σ* Γ* X* W)
        (match-define (-W Vs d) W)
        (with-guarded-arity 1 (l Γ* Vs)
          (match-define (list D) Vs)
          (define ℒ* (-ℒ-with-Γ ℒ Γ*))
          (define 𝒞 (-ℒ-hist ℒ))
          (define β (or (keep-if-const d) (-α.rng ℓ 𝒞)))
          (define-values (δσ αs cs) ; αs reverses Ws, which is reversed
            (for/fold ([δσ : -Δσ (hash β {set D})]
                       [αs : (Listof (U -α.cnst -α.dom)) '()]
                       [cs : (Listof -s) '()])
                      ([W Ws] [i : Natural (in-naturals)])
              (match-define (-W¹ C c) W)
              (define α (or (keep-if-const c) (-α.dom ℓ 𝒞 i)))
              (values (⊔ δσ α C) (cons α αs) (cons c cs))))
          (define G (-=> αs β ℓ))
          (define g (-?-> cs d))
          (values δσ {set (-ΓW Γ* (-W (list G) g))} ∅ ∅ ∅))))
     (⟦d⟧ M σ X ℒ))))

(: ↝.-->i : (Listof -W¹) (Listof -⟦e⟧) -W¹ -ℓ → -⟦ℰ⟧)
(define (((↝.-->i Ws ⟦c⟧s Mk-D ℓ) ⟦e⟧) M σ X ℒ)
  (apply/values
   (acc
    σ
    X
    (λ (ℰ) (-ℰ.-->i Ws ℰ ⟦c⟧s Mk-D ℓ))
    (λ (σ* Γ* X* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (define ℒ* (-ℒ-with-Γ ℒ Γ*))
        (match ⟦c⟧s
          [(cons ⟦c⟧ ⟦c⟧s*)
           (((↝.-->i Ws* ⟦c⟧s* Mk-D ℓ) ⟦c⟧) M σ* X* ℒ*)]
          ['()
           (mk-=>i ℒ* Ws* Mk-D ℓ)]))))
   (⟦e⟧ M σ X ℒ)))

(: mk-=>i : -ℒ (Listof -W¹) -W¹ -ℓ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) -ΔX (℘ -ℐ)))
;; Given *reversed* list of domains and range-maker, create indy contract
(define (mk-=>i ℒ Ws Mk-D ℓ)
  (match-define (-ℒ _ Γ 𝒞) ℒ)
  (define-values (δσ αs cs) ; `αs` and `cs` reverses `Ws`, which is reversed
    (for/fold ([δσ : -Δσ ⊥σ] [αs : (Listof (U -α.cnst -α.dom)) '()] [cs : (Listof -s) '()])
              ([(W i) (in-indexed Ws)])
      (match-define (-W¹ C c) W)
      (define α (or (keep-if-const c)
                    (-α.dom ℓ 𝒞 (assert i exact-nonnegative-integer?))))
      (values (⊔ δσ α C) (cons α αs) (cons c cs))))
  (match-define (-W¹ D d) Mk-D)
  (define γ (or (keep-if-const d) (-α.rng ℓ 𝒞)))
  (define δσ* (⊔ δσ γ D))
  (define C (-=>i αs γ ℓ))
  (define c (-?->i cs (and d (assert d -λ?))))
  (values δσ* {set (-ΓW Γ (-W (list C) c))} ∅ ∅ ∅))

(: ↝.case-> : Mon-Party -ℓ (Listof (Listof -W¹)) (Listof -W¹) (Listof -⟦e⟧) (Listof (Listof -⟦e⟧)) → -⟦ℰ⟧)
(define ((↝.case-> l ℓ Clauses Cs ⟦c⟧s clauses) ⟦c⟧)
  
  (λ (M σ X ℒ)
    (apply/values
     (acc
      σ
      X
      (λ (ℰ) (-ℰ.case-> l ℓ Clauses Cs ℰ ⟦c⟧s clauses))
      (λ (σ* Γ* X* W)
        (match-define (-W Vs s) W)
        (with-guarded-arity 1 (l Γ* Vs)
          (match-define (list C) Vs)
          (define Cs* (cons (-W¹ C s) Cs))
          (define ℒ* (-ℒ-with-Γ ℒ Γ*))
          (match ⟦c⟧s
            ['()
             (define Clauses* (cons Cs* Clauses))
             (match clauses
               ['()
                (error '↝.case-> "TODO")]
               [(cons clause clauses*)
                (error '↝.case-> "TODO")])]
            [(cons ⟦c⟧* ⟦c⟧s*)
             (((↝.case-> l ℓ Clauses Cs* ⟦c⟧s* clauses) ⟦c⟧*) M σ* X* ℒ*)]))))
     (⟦c⟧ M σ X ℒ))))

(: ↝.struct/c : -struct-info (Listof -W¹) (Listof -⟦e⟧) -ℓ → -⟦ℰ⟧)
(define (((↝.struct/c si Ws ⟦c⟧s ℓ) ⟦c⟧) M σ X ℒ)
  (apply/values
   (acc
    σ
    X
    (λ (ℰ) (-ℰ.struct/c si Ws ℰ ⟦c⟧s ℓ))
    (λ (σ* Γ* X* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (match ⟦c⟧s
          [(cons ⟦c⟧* ⟦c⟧s*)
           (((↝.struct/c si Ws* ⟦c⟧s* ℓ) ⟦c⟧*) M σ* X* (-ℒ-with-Γ ℒ Γ*))]
          ['()
           (define 𝒞 (-ℒ-hist ℒ))
           (define-values (δσ αs cs flat?) ; `αs` and `cs` reverse `Ws`, which is reversed
             (for/fold ([δσ : -Δσ ⊥σ]
                        [αs : (Listof (U -α.cnst -α.struct/c)) '()]
                        [cs : (Listof -s) '()]
                        [flat? : Boolean #t])
                       ([(W i) (in-indexed Ws*)])
               (match-define (-W¹ C c) W)
               (define α (or (keep-if-const c)
                             (-α.struct/c ℓ 𝒞 (assert i exact-nonnegative-integer?))))
               (values (⊔ δσ α C) (cons α αs) (cons c cs) (and flat? (C-flat? C)))))
           (define V (-St/C flat? si αs))
           (values δσ {set (-ΓW Γ* (-W (list V) (-?struct/c si cs)))} ∅ ∅ ∅)]))))
   (⟦c⟧ M σ X ℒ)))
