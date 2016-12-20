#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         racket/set
         racket/match)

(define/memo (↓ₓ [l : -l] [x : Symbol]) : -⟦e⟧
  (define -blm.undefined
    (-blm l 'Λ (list 'defined?) (list (format-symbol "~a_(~a)" 'undefined x))))
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-Σ σ _ _) Σ)
    (define α (ρ@ ρ x))
    (define old? (σ-old? σ α))
    (define s (and old? (canonicalize Γ x)))
    (cond
      [($@ $ s) =>
       (λ ([V : -V])
         (define V* (V+ σ V (predicates-of Γ s)))
         
         ;; Debugging
         #;(when (member x '(f₉ raw-filename))
           (printf "lookup: ~a: ~a~n - Γ: ~a~n~n"
                   (show-⟪α⟫ α) (show-V V*) (show-Γ Γ)))
         
         (⟦k⟧ (-W (list V*) s) ($+ $ s V*) Γ ⟪ℋ⟫ Σ))]
      [else
       (define Vs (σ@ σ α))
       (define φs (-Γ-facts Γ))
       
       ;; Debugging
       #;(when (member x '(c₁₅ s₉ c₁₆))
         (define Vs* (for/set: : (℘ -V) ([V Vs] #:when (plausible-V-s? φs V s)) V))
         (define-set root : -⟪α⟫ #:eq? #t)
         (printf "lookup: ~a (~a):~n" (show-⟪α⟫ α) (set-count Vs))
         (for ([V Vs*])
           (root-union! (V->⟪α⟫s V))
           (match V
             [(-Clo xs ⟦e⟧ ρ Γ)
              (printf "  - λ~a. ~a~n" (show-formals xs) (show-⟦e⟧ ⟦e⟧))
              (printf "     + ~a~n" (show-ρ ρ))
              (printf "     + ~a~n" (show-Γ Γ))]
             [_
              (printf "  - ~a~n" (show-V V))]))
         (printf "Γ: ~a~n" (show-Γ Γ))
         (printf "Others:~n")
         (for ([(α Vs) (hash-copy/spanning* (-σ-m σ) root V->⟪α⟫s)])
           (printf "  - ~a ↦ ~a~n" (show-⟪α⟫ (cast α -⟪α⟫)) (set-map Vs show-V)))
         (printf "~n"))
       
       (for/union : (℘ -ς) ([V Vs] #:when (plausible-V-s? φs V s))
         (define $* ($+ $ s V))
         (match V
           [(-b (not (? defined?))) (⟦k⟧ -blm.undefined $* Γ ⟪ℋ⟫ Σ)]
           [(-● ps) ; precision hack
            (define V* (V+ σ V (predicates-of Γ s)))
            (⟦k⟧ (-W (list V*) s) $* Γ ⟪ℋ⟫ Σ)]
           [_ (⟦k⟧ (-W (list V) s) $* Γ ⟪ℋ⟫ Σ)]))])))

(define ↓ₚᵣₘ : (-prim → -⟦e⟧)
  (let ([meq : (HashTable Any -⟦e⟧) (make-hasheq)] ; `eq` doesn't work for String but ok
        [m   : (HashTable Any -⟦e⟧) (make-hash  )])
    
    (: ret-p : -prim → -⟦e⟧)
    (define (ret-p p) (ret-W¹ p p))
    
    (match-lambda
      [(? symbol? o)  (hash-ref! meq o (λ () (ret-p o)))]
      [(and B (-b b)) (hash-ref! meq b (λ () (ret-p B)))]
      [p              (hash-ref! m   p (λ () (ret-p p)))])))

(define/memo (ret-W¹ [V : -V] [v : -s]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦k⟧ (-W (list V) v) $ Γ ⟪ℋ⟫ Σ)))

(define ⟦void⟧ (↓ₚᵣₘ -void))
(define ⟦tt⟧ (↓ₚᵣₘ -tt))
(define ⟦ff⟧ (↓ₚᵣₘ -ff))
