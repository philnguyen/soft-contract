#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/list
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt")

(: acc : -σ (-ℰ → -ℰ) (-σ -Γ -W → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
        → -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)
        → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
;; Bind-ish. Takes care of store widening.
;; Caller takes care of stack accumulation and what to do with result.
(define ((acc σ f comp) δσ ΓWs ΓEs ℐs)
  (define ℐs*
    (map/set
     (match-lambda
       [(-ℐ (-ℋ ℒ h xs    ℰ ) τ)
        (-ℐ (-ℋ ℒ h xs (f ℰ)) τ)])
     ℐs))
  (define σ* (⊔/m σ δσ))
  (for/fold ([δσ : -Δσ δσ] [ΓWs* : (℘ -ΓW) ∅] [ΓEs* : (℘ -ΓE) ΓEs] [ℐs* : (℘ -ℐ) ℐs*])
            ([ΓW ΓWs])
    (match-define (-ΓW Γ* W) ΓW)
    (define-values (δσ+ ΓWs+ ΓEs+ ℐs+) (comp σ* Γ* W))
    (values (⊔/m δσ δσ+) (∪ ΓWs* ΓWs+) (∪ ΓEs* ΓEs+) (∪ ℐs* ℐs+))))

(define-syntax-rule (with-guarded-arity n* (l Γ Vs) e ...)
  (let ([n n*]
        [m (length Vs)])
    (cond
      [(= n m) e ...]
      [else
       (define Cs (make-list n 'any/c))
       (values ⊥σ ∅ {set (-ΓE Γ (-blm l 'Λ Cs Vs))} ∅)])))

;; Memoized compilation of primitives because `Λ` needs a ridiculous number of these
(define ⇓ₚᵣₘ : (-prim → -⟦e⟧) 
  (let ([meq : (HashTable Any -⟦e⟧) (make-hasheq)] ; `eq` doesn't work for String but ok
        [m   : (HashTable Any -⟦e⟧) (make-hash  )])
    
    (: ret-p : -prim → -⟦e⟧)
    (define (ret-p p) (ret-W¹ (-W¹ p p)))
    
    (match-lambda
      [(? symbol? o)  (hash-ref! meq o (λ () (ret-p o)))]
      [(and B (-b b)) (hash-ref! meq b (λ () (ret-p B)))]
      [p              (hash-ref! m   p (λ () (ret-p p)))])))

(define/memo (ret-W¹ [W : -W¹]) : -⟦e⟧
  (match-define (-W¹ V v) W)
  (λ (M σ ℒ)
    (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅)))

(define ⟦void⟧ (⇓ₚᵣₘ -void))
(define ⟦tt⟧ (⇓ₚᵣₘ -tt))
(define ⟦ff⟧ (⇓ₚᵣₘ -ff))
