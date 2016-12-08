#lang typed/racket/base

;; This module provides runtime support for the def-prim DSL

(provide (all-defined-out))
(require racket/match
         racket/set
         "../../utils/set.rkt"
         "../../utils/list.rkt"
         "../../ast/definition.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

(define-type -⟦o⟧! (-⟪ℋ⟫ -ℓ -l -Σ -Γ (Listof -W¹) → (℘ -ΓA)))
(define-type Prim-Thunk (-Γ → (℘ -ΓA)))

(: unchecked-ac : -σ -st-ac -W¹ → (℘ -W¹))
;; unchecked struct accessor, assuming the value is already checked to be the right struct.
;; This is only for use internally, so it's safe (though imprecise) to ignore field wraps
(define (unchecked-ac σ ac W)
  (define-set seen : -⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-W¹ (list V) s) W)
  (match-define (-st-ac 𝒾 i) ac)
  (define s* (-?@ ac s))
  (let go ([V : -V V])
    (match V
      [(-St (== 𝒾) αs)
       (for/set: : (℘ -W¹) ([V* (in-set (σ@ σ (list-ref αs i)))])
         (-W¹ V* s*))]
      [(-St* (== 𝒾) _ α _)
       (cond [(seen-has? α) ∅]
             [else
              (seen-add! α)
              (for/union : (℘ -W¹) ([V (in-set (σ@ σ α))]) (go V))])]
      [(? -●?) {set (-W¹ -●/V s*)}]
      [_ ∅])))

(: ⊢?/quick : -R -σ -Γ -o -W¹ * → Boolean)
;; Perform a relatively cheap check (i.e. no SMT call) if `(o W ...)` returns `R`
(define (⊢?/quick R σ Γ o . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (eq? R (first-R (apply p∋Vs σ o Vs)
                  (Γ⊢e Γ (apply -?@ o ss)))))
