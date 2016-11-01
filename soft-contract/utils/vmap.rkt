#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "set.rkt")

(struct (X Y) VMap ([m : (HashTable X (Setof Y))] [version : Fixnum])
  #:transparent #:mutable)

(: ⊥vm (∀ (X Y) ([] [#:eq? Boolean #:init (Option (List X))] . ->* . (VMap X Y))))
(define (⊥vm #:eq? [use-eq? #f] #:init [x #f])
  (define mk (if use-eq? (inst hasheq X (℘ Y)) (inst hash X (℘ Y))))
  (define m
    (match x
      [(list k) (mk k ∅)]
      [_ (mk)]))
  (VMap m 0))

(: vm⊔! (∀ (X Y) (VMap X Y) X Y → Void))
(define (vm⊔! vm x y)
  (match-define (VMap m i) vm)
  (unless (∋ (hash-ref m x →∅) y)
    (set-VMap-m! vm (hash-update m x (λ ([ys : (℘ Y)]) (set-add ys y)) →∅))
    (set-VMap-version! vm (assert (+ 1 i) fixnum?))))

(: vm@ (∀ (X Y) (VMap X Y) X → (℘ Y)))
(define (vm@ vm x) (hash-ref (VMap-m vm) x →∅))
