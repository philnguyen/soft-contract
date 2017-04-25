#lang typed/racket/base

(provide make-indexed-set)

(require racket/set set-extras "unique.rkt")

(: make-indexed-set (∀ (X) (→ (Values Index
                                      (Index X → Index)
                                      ;; Debugging
                                      (Index → (℘ X))))))
;; Thin layer of `unique-nat` over (℘ X), with short-hand for addition
;; Let `n` be the number of `call-site` × `function-body`.
;; This is more compact than `bitset` for the average case where we don't have all 2ⁿ subsets.
;; But in the worst case, this caches all 2ⁿ subsets, while `bitset` only caches `n` elements.
(define (make-indexed-set)
  (define-values (f f⁻¹ _) ((inst unique-nat (℘ X))))

  (values
   ;; Empty
   (f ∅)
   ;; Set-add
   (λ (s x) (f (set-add (f⁻¹ s) x)))
   ;; Decode
   f⁻¹))

(module+ test
  (require typed/rackunit racket/set)
  (let*-values ([(mt add dc) ((inst make-indexed-set Symbol))]
                [(foo) (add mt 'foo)]
                [(foo-bar) (add foo 'bar)]
                [(foo-qux) (add foo 'qux)]
                [(foo-bar-qux) (add foo-bar 'qux)]
                [(foo-bar*) (add foo-bar 'foo)])
    (check-equal? foo-bar foo-bar*)
    (check-equal? (dc foo) {set 'foo})
    (check-equal? (dc foo-bar) {set 'foo 'bar})
    (check-equal? (dc foo-qux) (set 'foo 'qux))
    (check-equal? (dc foo-bar-qux) {set 'foo 'bar 'qux})
    (check-equal? (dc foo-bar*) {set 'foo 'bar})))
