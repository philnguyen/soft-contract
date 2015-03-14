#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics "lib.rkt" "lang.rkt" "tc.rkt" "z3.rkt"
         (prefix-in lo-tech: "proof-system.rkt"))

(define-relation SCPCF
  proves ⊆ Σ × L × P
  [(proves Σ L P)
   (where #t (lo-tech:proves Σ L P))]
  [(proves Σ L P)
   (where #t (lo-tech:neither Σ L P))
   (where ✓ (query (declare-Σ Σ) (translate-Σ Σ) (assert-L-P L P)))])

(define-relation SCPCF
  refutes ⊆ Σ × L × P
  [(refutes Σ L P)
   (where #t (lo-tech:refutes Σ L P))]
  [(refutes Σ L P)
   (where #t (lo-tech:neither Σ L P))
   (where ! (query (declare-Σ Σ) (translate-Σ Σ) (assert-L-P L P)))])

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
  (! {[0 ↦ 42] [1 ↦ 42]} 0 (λ (x : ℤ) (< x (↓ ℤ 1) Λ)))
  (✓ {[0 ↦ (• ℤ)]
      [1 ↦ (• ℤ (λ (x : ℤ) (> x (↓ ℤ 0) Λ)))]
      [2 ↦ (• ℤ (λ (x : ℤ) (≥ x (↓ ℤ 1) Λ)))]}
     2
     (λ (y : ℤ) (> y (↓ ℤ 0) Λ)))
  )
