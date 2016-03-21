#lang typed/racket/base

(provide mon)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt"
         "../proof-relation/main.rkt"
         "helpers.rkt"
         "continuation-if.rkt"
         "ap.rkt")

(: mon : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon l³ W-C W-V)
  (match-define (-W¹ C _) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  
  (λ (M σ ℬ)
    (define Γ (-ℬ-cnd ℬ))
    (case (MσΓ⊢V∈C M σ Γ W-C W-V)
      [(✓)
       (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) (-W (list V) v))} ∅ ∅)]
      [(✗)
       (values ⊥σ ∅ {set (-ΓE (-ℬ-cnd ℬ) (-blm l+ lo (list C) (list V)))} ∅)]
      [(?)
       (match C
         [(? -=>i? C) ((mon-=>i l³ C V) M σ ℬ)]
         [(-St/C _ s αs) ((mon-struct/c l³ s αs V) M σ ℬ)]
         [(-x/C α) ((mon-x/c l³ α V) M σ ℬ)]
         [(-And/C _ α₁ α₂) ((mon-and/c l³ α₁ α₂ V) M σ ℬ)]
         [(-Or/C  _ α₁ α₂) ((mon-or/c  l³ α₁ α₂ V) M σ ℬ)]
         [(-Not/C α) ((mon-not/c l³ α V) M σ ℬ)]
         [(-Vectorof α) ((mon-vectorof l³ α V) M σ ℬ)]
         [(-Vector/C αs) ((mon-vector/c l³ αs V) M σ ℬ)]
         [_ ((mon-flat l³ W-C W-V) M σ ℬ)])])))

(: mon-=>i : Mon-Info -=>i -V → -⟦e⟧)
(define (mon-=>i l³ C V)
  (error "TODO"))

(: mon-struct/c : Mon-Info -struct-info (Listof -α) -V → -⟦e⟧)
(define (mon-struct/c l³ s αs V)
  (error "TODO"))

(: mon-x/c : Mon-Info -α -V → -⟦e⟧)
(define (mon-x/c l³ α V)
  (error "TODO"))

(: mon-and/c : Mon-Info -α -α -V → -⟦e⟧)
(define (mon-and/c l³ α₁ α₂ V)
  (error "TODO"))

(: mon-or/c : Mon-Info -α -α -V → -⟦e⟧)
(define (mon-or/c l³ α₁ α₂ V)
  (error "TODO"))

(: mon-not/c : Mon-Info -α -V → -⟦e⟧)
(define (mon-not/c l³ α V)
  (error "TODO"))

(: mon-vectorof : Mon-Info -α -V → -⟦e⟧)
(define (mon-vectorof l³ α V)
  (error "TODO"))

(: mon-vector/c : Mon-Info (Listof -α) -V → -⟦e⟧)
(define (mon-vector/c l³ αs V)
  (error "TODO"))

(: mon-flat : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-flat l³ W-C W-V)
  (define ⟦e⟧ₒₖ (mk-⟦e⟧ₒₖ W-V))
  (define ⟦e⟧ₑᵣ (mk-⟦e⟧ₑᵣ l³ W-C W-V))
  (define lo (Mon-Info-src l³))
  ((↝.if lo ⟦e⟧ₒₖ ⟦e⟧ₑᵣ) (ap (Mon-Info-src l³) 0 W-C (list W-V))))

;; memoize these to avoid generating infinitely many compiled expressions
(define mk-⟦e⟧ₒₖ
  (with-memo (-W¹ → -⟦e⟧)
    (λ (W-V)
      (match-define (-W¹ V v) W-V)
      (λ (M σ ℬ)
        (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) (-W (list V) v))} ∅ ∅)))))
(define mk-⟦e⟧ₑᵣ
  (with-memo (Mon-Info -W¹ -W¹ → -⟦e⟧)
    (λ (l³ W-C W-V)
      (define C (-W¹-V W-C))
      (define V (-W¹-V W-V))
      (match-define (Mon-Info l+ _ lo) l³)
      (λ (M σ ℬ)
        (values ⊥σ ∅ {set (-ΓE (-ℬ-cnd ℬ) (-blm l+ lo (list C) (list V)))} ∅)))))
