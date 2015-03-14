#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics "lib.rkt" "lang.rkt" "tc.rkt")

(define-relation SCPCF
  proves ⊆ Σ × L × P
  [(proves Σ L (λ (X : ℤ) (zero? X _)))
   (where 0 (@ Σ L))]
  [(proves Σ L (λ (X : ℤ) (O X _)))
   (where (• ℤ _ ... (λ (Y : ℤ) (O Y _)) _ ...) (@ Σ L))]
  [(proves Σ L (λ (X : ℤ) (zero? E _)))
   (refutes Σ L (λ (X : ℤ) E))]
  [(proves Σ L_1 (λ (X : ℤ) (< X (↓ ℤ L_2) _)))
   (where n_1 (@ Σ L_1))
   (where n_2 (@ Σ L_2))
   (side-condition (< (term n_1) (term n_2)))]
  [(proves Σ L_1 (λ (X : ℤ) (= X (↓ ℤ L_2) _)))
   (where n (@ Σ L_1))
   (where n (@ Σ L_2))])

(define-relation SCPCF
  refutes ⊆ Σ × L × P
  [(refutes Σ L (λ (X : ℤ) (zero? X _)))
   (where n (@ Σ L))
   (side-condition (not (zero? (term n))))]
  [(refutes Σ L (λ (X : ℤ) (O X _)))
   (where (• ℤ _ ... (λ (Y : ℤ) (zero? (O X _) _))) (@ Σ L))]
  [(refutes Σ L (λ (X : ℤ) (zero? E _)))
   (proves Σ L (λ (X : ℤ) E))]
  [(refutes Σ L_1 (λ (X : ℤ) (< X (↓ ℤ L_2) _)))
   (where n_1 (@ Σ L_1))
   (where n_2 (@ Σ L_2))
   (side-condition (>= (term n_1) (term n_2)))]
  [(refutes Σ L_1 (λ (X : ℤ) (= X (↓ ℤ L_2) _)))
   (where n_1 (@ Σ L_1))
   (where n_2 (@ Σ L_2))
   (side-condition (not (= (term n_1) (term n_2))))])

(define-relation SCPCF
  neither ⊆ Σ × L × P
  [(neither Σ L P)
   (where #f (proves Σ L P))
   (where #f (refutes Σ L P))])

(module+ test
  (require rackunit)

  (define-syntax-rule (✓ Σ L P)
    (test-case (format "~a ⊢ ~a : ~a ✓" (term Σ) (term L) (term P))
      (check-true (term (proves Σ L P)))
      (check-false (term (refutes Σ L P)))
      (check-false (term (neither Σ L P)))))

  (define-syntax-rule (! Σ L P)
    (test-case (format "~a ⊢ ~a : ~a X" (term Σ) (term L) (term P))
      (check-false (term (proves Σ L P)))
      (check-true (term (refutes Σ L P)))
      (check-false (term (neither Σ L P)))))

  (define-syntax-rule (? Σ L P)
    (test-case (format "~a ⊢ ~a : ~a ?" (term Σ) (term L) (term P))
      (check-false (term (proves Σ L P)))
      (check-false (term (refutes Σ L P)))
      (check-true (term (neither Σ L P)))))

  (✓ {[0 ↦ 0]} 0 Zero?)
  (! {[0 ↦ 1]} 0 Zero?)
  (? {[0 ↦ (• ℤ)]} 0 Zero?)
  (✓ {[0 ↦ (• ℤ Zero?)]} 0 Zero?)
  (! {[0 ↦ (• ℤ (¬/P Zero?))]} 0 Zero?)
  (✓ {[0 ↦ 41] [1 ↦ 42]} 0 (λ (x : ℤ) (< x (↓ ℤ 1) Λ)))
  (! {[0 ↦ 41] [1 ↦ 42]} 1 (λ (x : ℤ) (< x (↓ ℤ 1) Λ)))
  (! {[0 ↦ 42] [1 ↦ 42]} 0 (λ (x : ℤ) (< x (↓ ℤ 1) Λ))))
