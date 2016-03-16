#lang typed/racket/base

(provide make-bitset make-indexed-set)

(require racket/set "unique.rkt" "set.rkt")

(: make-bitset (∀ (X) (→ (Values (Integer X → Integer)
                                 (Integer X → Boolean)
                                 ; for debugging only
                                 (Integer → (Listof X))))))
;; Create a bit-set for `X`. No guarantee about consistency across multiple program runs.
(define (make-bitset)
  (define-values (x->ith ith->x _) ((inst unique-nat X) #:hacked-warning 4096))

  (values
   ;; Add
   (λ (bs x)
     (bitwise-ior bs (arithmetic-shift 1 (x->ith x))))
   ;; Check
   (λ (bs x)
     (bitwise-bit-set? bs (x->ith x)))
   ;; Decode
   (λ (bs)
     (for/list ([i (integer-length bs)]
                #:when (bitwise-bit-set? bs i))
      (ith->x i)))))

(module+ test
  (require typed/rackunit racket/set)

  (let-values ([(add has? bs->xs) ((inst make-bitset Symbol))])
    (define n (add (add (add 0 'foo) 'bar) 'qux))
    (check-true (has? n 'foo))
    (check-true (has? n 'bar))
    (check-true (has? n 'qux))
    (check-false (has? n 'nope))
    (check-equal? (list->set (bs->xs n)) {set 'foo 'bar 'qux}))
  )

(: make-indexed-set (∀ (X) (→ (Values Natural
                                      (Natural X → Natural)
                                      ;; Debugging
                                      (Natural → (℘ X))))))
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
