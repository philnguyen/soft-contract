#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/list
         racket/set
         "../utils/main.rkt"
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
       [(-ℐ (-ℋ ρ Γ s 𝒳    ℰ ) ℬ)
        (-ℐ (-ℋ ρ Γ s 𝒳 (f ℰ)) ℬ)])
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
