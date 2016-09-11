#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "set.rkt")

(struct (X Y) VMap ([m : (HashTable X (Setof Y))] [version : Fixnum])
  #:transparent #:mutable)

(: ⊥vm (∀ (X Y) ([] [#:eq? Boolean] . ->* . (VMap X Y))))
(define (⊥vm #:eq? [use-eq? #f])
  (define mk (if use-eq? (inst make-hasheq X (℘ Y)) (inst make-hash X (℘ Y))))
  (VMap (mk) 0))

(: vm⊔! (∀ (X Y) (VMap X Y) X Y → Void))
(define (vm⊔! vm x y)
  (match-define (VMap m i) vm)
  (unless (∋ (hash-ref m x →∅) y)
    (hash-update! m x (λ ([ys : (℘ Y)]) (set-add ys y)) →∅)
    (set-VMap-version! vm (assert (+ 1 i) fixnum?))))

(: vm@ (∀ (X Y) (VMap X Y) X → (℘ Y)))
(define (vm@ vm x) (hash-ref (VMap-m vm) x →∅))
