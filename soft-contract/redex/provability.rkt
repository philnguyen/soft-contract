#lang racket/base
(require racket/set redex/reduction-semantics racket/contract "lib.rkt" "syntax.rkt")
(provide (all-defined-out))

;; Not always use global table `M`, so make it a parameter for lighter syntax
(define/contract -M (parameter/c (redex-match? L M))
  (make-parameter (term ⊥)))

;; Γ ⊢ e : (✓|X|?)
(define-relation L
  Γ⊢ ⊆ Γ × ?e × R
  ; Proves
  [(Γ⊢ _ e ✓+X)
   (e⊢₀ e ✓+X)]
  [(Γ⊢ Γ e ✓+X)
   (∈ e* Γ)        (e⊢ e* e ✓+X)]
  ; Neither
  [(Γ⊢ _ #f ?)]
  [(Γ⊢ Γ e ?)
   (side-condition (not (term (Γ⊢ Γ e ✓))))
   (side-condition (not (term (Γ⊢ Γ e X))))])

;; e ⊢ e : (✓|X|?)
(define-relation L
  e⊢ ⊆ e × e × R
  [(e⊢ _ e ✓+X)
   (e⊢₀ e ✓+X)]
  ;; definitely proves
  [(e⊢ e e ✓)]
  [(e⊢ e (not e*) ✓)
   (e⊢ e e* X)]
  [(e⊢ (cons? e) e ✓)]
  [(e⊢ (procedure? e) e ✓)]
  ;; definitely refutes
  [(e⊢ e (not e*) X)
   (e⊢ e e* ✓)]
  [(e⊢ (not e) e X)]
  ;; who knows
  [(e⊢ e e* ?)
   (side-condition (not (term (e⊢ e e* ✓))))
   (side-condition (not (term (e⊢ e e* X))))])
;; ⊢ e : (✓|x|?)
(define-relation L
  e⊢₀ ⊆ e × R
  ;; definitly evals to non-#f
  [(e⊢₀ b ✓)
   (side-condition (not (equal? 0 (term b))))]
  [(e⊢₀ (add1 n) ✓)
   (side-condtion (not (= -1 (term n))))]
  [(e⊢₀ (cons _ _) ✓)]
  [(e⊢₀ (λ (x) e) ✓)]
  [(e⊢₀ (equal? e e) ✓)]
  [(e⊢₀ (not e) ✓)
   (e⊢₀ e X)]
  ;; definitley evals to #f
  [(e⊢₀ 0 X)]
  [(e⊢₀ (add1 -1) X)]
  [(e⊢₀ (not e) X)
   (e⊢₀ e ✓)]
  ;; who knows
  [(e⊢₀ e ?)
   (side-condition (not (term (e⊢₀ e ✓))))
   (side-condition (not (term (e⊢₀ e X))))])

(define-judgment-form L
  #:contract (Γ⊓ Γ e Γ)
  #:mode     (Γ⊓ I I O )
  [(Γ⊢ Γ e ✓)
   ----------------------------------------- "Γ⊓-redundant"
   (Γ⊓ Γ e Γ)]
  [(Γ⊢ Γ e ?)
   (set-split Γ Γ* e*)
   (e⊢ e e* ✓)
   ----------------------------------------- "Γ⊓-strengthen"
   (Γ⊓ Γ e ,(set-add (term Γ*) (term e)))])

(module+ test
  (require rackunit)
  (define-syntax-rule (check-Γ⊢-✓ Γ e)
    (begin
      (check-true  (term (Γ⊢ Γ e ✓)))
      (check-false (term (Γ⊢ Γ e X)))
      (check-false (term (Γ⊢ Γ e ?)))))
  (define-syntax-rule (check-Γ⊢-X Γ e)
    (begin
      (check-false (term (Γ⊢ Γ e ✓)))
      (check-true  (term (Γ⊢ Γ e X)))
      (check-false (term (Γ⊢ Γ e ?)))))
  (define-syntax-rule (check-Γ⊢-? Γ e)
    (begin
      (check-false (term (Γ⊢ Γ e ✓)))
      (check-false (term (Γ⊢ Γ e X)))
      (check-true  (term (Γ⊢ Γ e ?)))))
  (check-Γ⊢-✓ ∅ 42)
  (check-Γ⊢-✓ ∅ (add1 2))
  (check-Γ⊢-✓ ∅ (cons 1 2))
  (check-Γ⊢-✓ ∅ (not 0))
  (check-Γ⊢-✓ {S+ x} x)
  (check-Γ⊢-✓ {S+ x} (not (not x)))
  (check-Γ⊢-X ∅ 0)
  (check-Γ⊢-X ∅ (not 42))
  (check-Γ⊢-X ∅ (not (add1 2)))
  (check-Γ⊢-X {S+ (not x)} x)
  (check-Γ⊢-X {S+ (not x)} (not (not x)))
  (check-Γ⊢-? {S+ z} (f x)))

;; V⊢ V V : (✓|X|?)
(define-relation L
  V⊢ ⊆ V × o? × R
  ;; proves
  [(V⊢ (Clo _ _ _ _) procedure? ✓)]
  [(V⊢ (Cons _ _) cons? ✓)]
  [(V⊢ n integer? ✓)]
  [(V⊢ 0 not ✓)]
  ;; refutes
  [(V⊢ (Clo _ _ _ _) o? X)
   (side-condition (not (equal? (term o?) 'procedure?)))]
  [(V⊢ (Cons _ _) o? X)
   (side-condition (not (equal? (term o?) 'cons?)))]
  [(V⊢ n o? X)
   (side-condition (and (not (equal? (term n) 0))
                        (not (equal? (term o?) 'integer?))))]
  [(V⊢ 0 o? X)
   (side-condition (not (member (term o?) '(integer? zero?))))]
  [(V⊢ ● _ ?)])

;; Checks whether Γ refutes (x = V)
(define-relation L
  spurious? ⊆ ?e × V × Γ
  [(spurious? ?e (Cons _ _) Γ)
   (where {_ ... (o? ?e) _ ...} ,(set->list (term Γ)))
   (side-condition (not (equal? (term o?) 'cons?)))]
  [(spurious? ?e (Clo _ _ _ _) Γ)
   (where {_ ... (o? ?e) _ ...} ,(set->list (term Γ)))
   (side-condition (not (equal? (term o?) 'procedure?)))]
  [(spurious? ?e n Γ)
   (where {_ ... (o? ?e) _ ...} ,(set->list (term Γ)))
   (side-condition (not (zero? (term n))))
   (side-condition (not (equal? (term o?) 'integer?)))]
  [(spurious? ?e 0 Γ)
   (where {_ ... (o? ?e) _ ...} ,(set->list (term Γ)))
   (side-condition (not (member (term o?) '(integer? not))))]
  [(spurious? ?e 0 Γ)
   (∈ ?e Γ)]
  )
