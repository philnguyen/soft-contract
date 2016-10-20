#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         racket/set
         racket/match)

(define/memo (↓ₓ [l : -l] [x : Var-Name]) : -⟦e⟧!
  (define -blm.undefined (-blm l 'Λ (list 'defined?) (list 'undefined)))
  (λ (ρ Γ 𝒞 Σ ⟦k⟧)
    (define α (ρ@ ρ x))
    (match-define (-Σ σ _ _) Σ)
    (define-values (Vs old?) (σ@ σ α))
    (define s (and old? (canonicalize Γ x)))
    (define φs (-Γ-facts Γ))
    #;(when (∋ x {set 'n 'm 'x})
      (printf "lookup: ~a -> ~a~n" (show-Var-Name x) (set-map Vs show-V)))
    (for/union : (℘ -ς) ([V Vs] #:when (plausible-V-s? φs V s))
      (match V
        ['undefined (⟦k⟧ -blm.undefined Γ 𝒞 Σ)]
        [(-● ps) ; precision hack
         (define V* (V+ σ V (predicates-of Γ s)))
         (⟦k⟧ (-W (list V*) s) Γ 𝒞 Σ)]
        [_ (⟦k⟧ (-W (list V) s) Γ 𝒞 Σ)]))))

(define ↓ₚᵣₘ : (-prim → -⟦e⟧!)
  (let ([meq : (HashTable Any -⟦e⟧!) (make-hasheq)] ; `eq` doesn't work for String but ok
        [m   : (HashTable Any -⟦e⟧!) (make-hash  )])
    
    (: ret-p : -prim → -⟦e⟧!)
    (define (ret-p p) (ret-W¹ p p))
    
    (match-lambda
      [(? symbol? o)  (hash-ref! meq o (λ () (ret-p o)))]
      [(and B (-b b)) (hash-ref! meq b (λ () (ret-p B)))]
      [p              (hash-ref! m   p (λ () (ret-p p)))])))

(define/memo (ret-W¹ [V : -V] [v : -s]) : -⟦e⟧!
  (λ (ρ Γ 𝒞 Σ ⟦k⟧)
    (⟦k⟧ (-W (list V) v) Γ 𝒞 Σ)))

(define ⟦void⟧ (↓ₚᵣₘ -void))
(define ⟦tt⟧ (↓ₚᵣₘ -tt))
(define ⟦ff⟧ (↓ₚᵣₘ -ff))
