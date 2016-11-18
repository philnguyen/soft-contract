#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "set.rkt")

(define-type Map HashTable)
(define-type (MMap X Y) (Map X (℘ Y)))

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) ([(Map X Y)] [#:eq? Boolean] . ->* . (℘ X))))
(define (dom f #:eq? [use-eq? #f])
  (if use-eq?
      (for/seteq: : (℘ X) ([x (in-hash-keys f)]) x)
      (for/set:   : (℘ X) ([x (in-hash-keys f)]) x)))

(: ⊔ : (∀ (X Y) (MMap X Y) X Y → (MMap X Y)))
;; m ⊔ [x ↦ {y}]
(define (⊔ m x y)
  (hash-update m x (λ ([ys : (℘ Y)]) (set-add ys y)) →∅))

(define-syntax ⊔*
  (syntax-rules (↦)
    [(_ m) m]
    [(_ m [x ↦ y] p ...) (⊔* (⊔ m x y) p ...)]))

(: ⊔! : (∀ (X Y) ((MMap X Y) X Y → Void)))
;; mutate `m` to `m ⊔ [x ↦ {y}]`
(define (⊔! m x y)
  (hash-update! m x (λ ([s : (℘ Y)]) (set-add s y)) →∅))

(define-syntax ⊔*!
  (syntax-rules (↦)
    [(_ _) (void)]
    [(_ m [x ↦ y] p ...)
     (begin
       (⊔!  m x y)
       (⊔!* m p ...))]))

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

(: m↓ : (∀ (X Y) (HashTable X Y) (℘ X) → (HashTable X Y)))
;; Restrict map to given domain
(define (m↓ m xs)
  (cond
    [(and (immutable? m) (hash-eq? m))
     (for/hasheq : (Map X Y) ([(k v) m] #:when (∋ xs k))
       (values k v))]
    [(immutable? m)
     (for/hash : (Map X Y) ([(k v) m] #:when (∋ xs k))
       (values k v))]
    [else ; mutable
     (define m* : (HashTable X Y) (if (hash-eq? m) (make-hasheq) (make-hash)))
     (for ([(k v) m] #:when (∋ xs k))
       (hash-set! m* k v))
     m*]))

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

(: span (∀ (X Y) ([(HashTable X Y) (℘ X) (Y → (℘ X))] [#:eq? Boolean] . ->* . (℘ X))))
(define (span m root f #:eq? [use-eq? #f])
  (define-set touched : X #:eq? use-eq?)
  (define (touch! [x : X]) : Void
    (unless (touched-has? x)
      (touched-add! x)
      (set-for-each (f (hash-ref m x)) touch!)))
  (set-for-each root touch!)
  touched)

(: span* (∀ (X Y) ([(MMap X Y) (℘ X) (Y → (℘ X))] [#:eq? Boolean] . ->* . (℘ X))))
(define (span* m root f #:eq? [use-eq? #f])
  (span m root
        (if use-eq?
            (λ ([ys : (℘ Y)])
              (for/unioneq : (℘ X) ([y ys]) (f y)))
            (λ ([ys : (℘ Y)])
              (for/union : (℘ X) ([y ys]) (f y))))
        #:eq? use-eq?))

(: mk-interner (∀ (X) ([] [#:eq? Boolean] . ->* . (X → Index))))
;; Intern something as integers
(define (mk-interner #:eq? [use-eq? #f])
  (define m : (HashTable X Index) ((if use-eq? make-hasheq make-hash)))
  (λ (x) (hash-ref! m x (λ () (hash-count m)))))

;; For inspecting shared addresses
(: mmap-keep-min
   (∀ (X Y) ([(MMap X Y)] [Natural] . ->* . (Values (MMap X Y) (HashTable X Natural)))))
(define (mmap-keep-min m [n 2])
  (define m↓
    (for/hash : (MMap X Y) ([(x ys) m] #:when (>= (set-count ys) n))
      (values x ys)))
  (define counts
    (for/hash : (HashTable X Natural) ([(x ys) m↓])
      (values x (set-count ys))))
  (values m↓ counts))

(: hash-copy/spanning (∀ (X Y) (HashTable X Y) (℘ X) (Y → (℘ X)) → (HashTable X Y)))
(define (hash-copy/spanning m xs y->xs)
  (define-set touched : X)
  (define m* : (HashTable X Y) (if (hash-eq? m) (make-hasheq) (make-hash)))
  (define (touch! [x : X]) : Void
    (unless (touched-has? x)
      (touched-add! x)
      (define y (hash-ref m x))
      (hash-set! m* x y)
      (set-for-each (y->xs y) touch!)))
  (set-for-each xs touch!)
  m*)

(: hash-copy/spanning*
   (∀ (X Y) (HashTable X (℘ Y)) (℘ X) (Y → (℘ X)) → (HashTable X (℘ Y))))
(define (hash-copy/spanning* m xs y->xs)
  (hash-copy/spanning m xs (λ ([ys : (℘ Y)]) (for/union : (℘ X) ([y ys]) (y->xs y)))))


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
