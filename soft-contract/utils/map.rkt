#lang typed/racket/base

(provide
 Map MMap NeListof ΔMap
 dom ⊔ ⊔! ⊔* ⊔!* ⊔/m m∋ m@ Δ+ mmap-subtract)

(require racket/match racket/set "set.rkt")

(define-type Map HashTable)
(define-type (MMap X Y) (Map X (Setof Y)))
(define-type (NeListof X) (Pairof X (Listof X)))
(define-type (ΔMap X Y) (Listof (Pairof X Y)))

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) (Map X Y) → (Setof X)))
(define (dom f)
  (list->set (hash-keys f)))

(: ⊔ : (∀ (X Y) (MMap X Y) X Y → (MMap X Y)))
;; m ⊔ [x ↦ {y}]
(define (⊔ m x y)
  (hash-update m x (λ ([ys : (Setof Y)]) (set-add ys y)) →∅))

(: ⊔! : (∀ (X Y) ((MMap X Y) X Y → Void)))
;; mutate `m` to `m ⊔ [x ↦ {y}]`
(define (⊔! m x y)
  (hash-update! m x (λ ([s : (Setof Y)]) (set-add s y)) →∅))

(: ⊔* : (∀ (X Y) (MMap X Y) X (Setof Y) → (MMap X Y)))
;; m ⊔ [x ↦ ys]
(define (⊔* m x ys)
  (hash-update m x (λ ([s : (Setof Y)]) (∪ s ys)) →∅))

(: ⊔!* : (∀ (X Y) (MMap X Y) X (Setof Y) → Void))
;; mutate `m` to `m ⊔ [x ↦ ys]`
(define (⊔!* m x ys)
  (hash-update! m x (λ ([s : (Setof Y)]) (∪ s ys)) →∅))

(: ⊔/m : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
(define (⊔/m m₁ m₂)
  (for/fold ([m : (MMap X Y) m₁]) ([(x ys) (in-hash m₂)])
    (⊔* m x ys)))

(: Δ+ : (∀ (X Y) (ΔMap X Y) (MMap X Y) → (Values (MMap X Y) Boolean)))
;; Apply map delta to map
(define (Δ+ Δ m)
  (for/fold ([m : (MMap X Y) m] [δ? : Boolean #f]) ([δ Δ])
    (match-define (cons k v) δ)
    (values (⊔ m k v) (or δ? (not (m∋ m k v))))))

(: mmap-subtract : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
;; Compute bindings in `m₁` not in `m₀`
(define (mmap-subtract m₁ m₀)
  (for/fold ([acc : (MMap X Y) (hash)]) ([(k v) (in-hash m₁)])
    (define δv (set-subtract v (m@ m₀ k)))
    (if (set-empty? δv) acc (hash-set acc k δv))))

(: m∋ (∀ (X Y) (MMap X Y) X Y → Boolean))
(define (m∋ m x y) (∋ (m@ m x) y))

(: m@ (∀ (X Y) (MMap X Y) X → (Setof Y)))
(define (m@ m x) (hash-ref m x →∅))
