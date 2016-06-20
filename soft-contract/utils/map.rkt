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
  (cond
    [(hash-eq? m)
     (for/hasheq : (Map X Y) ([(k v) m] #:when (∋ xs k))
       (values k v))]
    [else
     (for/hash : (Map X Y) ([(k v) m] #:when (∋ xs k))
       (values k v))]))

(: hash-merge (∀ (X Y) (HashTable X Y) (HashTable X Y) → (HashTable X Y)))
(define (hash-merge m₁ m₂)
  (for/fold ([m : (HashTable X Y) m₁]) ([(k v) m₂])
    (hash-set m k v)))

(: map/hash (∀ (X Y Z) (Y → Z) (HashTable X Y) → (HashTable X Z)))
(define (map/hash f m)
  (cond
    [(hash-eq? m)
     (for/hasheq : (HashTable X Z) ([(x y) m])
       (values x (f y)))]
    [else
     (for/hash : (HashTable X Z) ([(x y) m])
       (values x (f y)))]))

(: span (∀ (X Y) (MMap X Y) (℘ X) (Y → (℘ X)) → (℘ X)))
(define (span m xs₀ f)
  (define-set touched : X)
  (define (go! [x : X]) : Void
    (cond
      [(∋ touched x) (void)]
      [else
       (touched-add! x)
       (for ([y (in-set (hash-ref m x))])
         (go*! (f y)))]))
  (define (go*! [xs : (℘ X)]) : Void
    (for ([x (in-set xs)])
      (go! x)))
  (go*! xs₀)
  touched)

(: mk-interner (∀ (X) ([] [#:eq? Boolean] . ->* . (X → Natural))))
;; Intern something as integers
(define (mk-interner #:eq? [use-eq? #f])
  (define m : (HashTable X Natural) ((if use-eq? make-hasheq make-hash)))
  (λ (x) (hash-ref! m x (λ () (hash-count m)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; TMP hack for profiling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define data : (Listof (Pairof Any Integer)) '())
(define (accum-data! [d : Any] [n : Integer])
  (set! data (cons (cons d n) data)))

(require racket/list)
(define (extract-best) : (Listof (Pairof Any Integer))
  (define data* : (Listof (Pairof Any Integer))
    (sort
     data
     (λ ([x₁ : (Pairof Any Integer)] [x₂ : (Pairof Any Integer)])
       (> (cdr x₁) (cdr x₂)))))
  (take data* (min (length data*) 20)))
