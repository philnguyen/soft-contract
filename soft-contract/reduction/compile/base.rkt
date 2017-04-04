#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         racket/set
         racket/match)

(define/memo (↓ₓ [l : -l] [x : Symbol]) : -⟦e⟧
  (define -blm.undefined ; TODO should have had attached location to `x` too?
    (-blm l 'Λ (list 'defined?) (list (format-symbol "~a_(~a)" 'undefined x)) +ℓ₀))
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-Σ σ _ _) Σ)
    (define α (ρ@ ρ x))
    (define tₓ (and (not (mutated? σ α)) (canonicalize Γ x)))
    (cond
      [($@ $ (or tₓ (-x x))) =>
       (λ ([V : -V])
         (cond [(plausible-V-t? (-Γ-facts Γ) V tₓ)
                (define V* (V+ σ V (predicates-of Γ tₓ)))
                (⟦k⟧ (-W (list V*) tₓ) ($+ $ tₓ V*) Γ ⟪ℋ⟫ Σ)]
               [else ∅]))]
      [else
       (define Vs (σ@ σ α))
       (define φs (-Γ-facts Γ))
       
       (for/union : (℘ -ς) ([V Vs] #:when (plausible-V-t? φs V tₓ))
         (define $* ($+ $ (or tₓ (-x x)) V))
         (match V
           [(-b (not (? defined?))) (⟦k⟧ -blm.undefined $* Γ ⟪ℋ⟫ Σ)]
           [(-● ps) ; precision hack
            (define V* (V+ σ V (predicates-of Γ tₓ)))
            (⟦k⟧ (-W (list V*) tₓ) $* Γ ⟪ℋ⟫ Σ)]
           [_ (⟦k⟧ (-W (list V) tₓ) $* Γ ⟪ℋ⟫ Σ)]))])))

(define ↓ₚᵣₘ : (-prim → -⟦e⟧)
  (let ([meq : (HashTable Any -⟦e⟧) (make-hasheq)] ; `eq` doesn't work for String but ok
        [m   : (HashTable Any -⟦e⟧) (make-hash  )])
    
    (: ret-p : -prim → -⟦e⟧)
    (define (ret-p p) (ret-W¹ p p))
    
    (match-lambda
      [(? symbol? o)  (hash-ref! meq o (λ () (ret-p o)))]
      [(and B (-b b)) (hash-ref! meq b (λ () (ret-p B)))]
      [p              (hash-ref! m   p (λ () (ret-p p)))])))

(define/memo (ret-W¹ [V : -V] [t : -?t]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦k⟧ (-W (list V) t) $ Γ ⟪ℋ⟫ Σ)))

(define ⟦void⟧ (↓ₚᵣₘ -void))
(define ⟦tt⟧ (↓ₚᵣₘ -tt))
(define ⟦ff⟧ (↓ₚᵣₘ -ff))
