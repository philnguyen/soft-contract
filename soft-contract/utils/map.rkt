#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "set.rkt")

(define-type Map HashTable)
(define-type (MMap X Y) (Map X (℘ Y)))

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) (Map X Y) → (℘ X)))
(define (dom f)
  (for/set: : (℘ X) ([x (in-hash-keys f)]) x))

(: ⊔ : (∀ (X Y) (MMap X Y) X Y → (MMap X Y)))
;; m ⊔ [x ↦ {y}]
(define (⊔ m x y)
  (hash-update m x (λ ([ys : (℘ Y)]) (set-add ys y)) →∅))

(: ⊔! : (∀ (X Y) ((MMap X Y) X Y → Void)))
;; mutate `m` to `m ⊔ [x ↦ {y}]`
(define (⊔! m x y)
  (hash-update! m x (λ ([s : (℘ Y)]) (set-add s y)) →∅))

(define-syntax ⊔*
  (syntax-rules ()
    [(_ m) m]
    [(_ m [x y] p ...) (⊔* (⊔ m x y) p ...)]))

(: ⊔!* : (∀ (X Y) (MMap X Y) X (℘ Y) → Void))
;; mutate `m` to `m ⊔ [x ↦ ys]`
(define (⊔!* m x ys)
  (hash-update! m x (λ ([s : (℘ Y)]) (∪ s ys)) →∅))

(: ⊔/m : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
(define (⊔/m m₁ m₂)
  (for/fold ([m : (MMap X Y) m₁]) ([(x ys) (in-hash m₂)])
    (hash-update m x (λ ([s : (℘ Y)]) (∪ s ys)) →∅)))

(: mmap-subtract : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
;; Compute bindings in `m₁` not in `m₀`
(define (mmap-subtract m₁ m₀)
  (for/fold ([acc : (MMap X Y) (hash)]) ([(k v) (in-hash m₁)])
    (define δv (set-subtract v (m@ m₀ k)))
    (if (set-empty? δv) acc (hash-set acc k δv))))

(: m∋ (∀ (X Y) (MMap X Y) X Y → Boolean))
(define (m∋ m x y) (∋ (m@ m x) y))

(: m@ (∀ (X Y) (MMap X Y) X → (℘ Y)))
(define (m@ m x) (hash-ref m x →∅))

(: m↓ : (∀ (X Y) (Map X Y) (℘ X) → (Map X Y)))
;; Restrict map to given domain
(define (m↓ m xs)
  (for/hash : (Map X Y) ([(k v) m] #:when (∋ xs k))
    (values k v)))

(: hash-merge (∀ (X Y) (HashTable X Y) (HashTable X Y) → (HashTable X Y)))
(define (hash-merge m₁ m₂)
  (for/fold ([m : (HashTable X Y) m₁]) ([(k v) m₂])
    (hash-set m k v)))
