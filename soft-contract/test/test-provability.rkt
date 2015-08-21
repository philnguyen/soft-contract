#lang racket/base

(module+ test
  (require rackunit "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt")
  (define-syntax-rule (check-✓ e) (check-equal? e '✓))
  (define-syntax-rule (check-X e) (check-equal? e 'X))
  (define-syntax-rule (check-? e) (check-equal? e '?))

  ;; V ∈ p
  (check-✓ (V∈p (-b #f) 'false?))
  (check-✓ (V∈p (-b #f) 'boolean?))
  (check-✓ (V∈p (-b 1) 'integer?))
  (check-✓ (V∈p (-b 1) 'real?))
  (check-✓ (V∈p (-b 1) 'number?))
  (check-✓ (V∈p (-Clo '(x) (-b 1) -ρ∅ -Γ∅) 'procedure?))
  (check-✓ (V∈p 'procedure? 'procedure?))
  (check-✓ (V∈p (-St (-id 'cons 'Λ) (list (-α.val (-b 1)) (-α.val (-b 2)))) -cons?))
  (check-X (V∈p (-St (-id 'cons 'Λ) (list (-α.val (-b 1)) (-α.val (-b 2)))) 'number?))
  (check-X (V∈p (-b 1.5) 'integer?))
  (check-X (V∈p (-b 1+1i) 'real?))
  (check-? (V∈p '• 'integer?))

  ;; ⊢ e
  (check-✓ (⊢e 'false?))
  (check-✓ (⊢e (-b 0)))
  (check-X (⊢e (-b #f)))
  (check-? (⊢e (-x 'x)))
  (check-X (⊢e (-@ 'false? (list (-b 0)) '†)))
  (check-✓ (⊢e (-@ 'equal? (list (-x 'x) (-x 'x)) '†)))
  (check-✓ (⊢e (-@ '+ (list (-x 'x) (-x 'y)) '†)))

  ;; e ⊢ e
  (check-✓ (e⊢e (-b #f) (-b #f)))
  (check-✓ (e⊢e (-@ -cons? (list (-x 'x)) '†) (-x 'x)))
  (check-✓ (e⊢e (-@ 'integer? (list (-x 'x)) '†)
                (-@ 'real? (list (-x 'x)) '†)))
  (check-✓ (e⊢e (-@ 'false? (list (-@ 'number? (list (-x 'x)) '†)) '†)
                (-@ 'false? (list (-@ 'integer? (list (-x 'x)) '†)) '†)))
  (check-X (e⊢e (-@ 'false? (list (-x 'x)) '†) (-x 'x)))
  (check-? (e⊢e (-@ 'number? (list (-x 'x)) '†)
                (-@ 'integer? (list (-x 'x)) '†)))

  )
