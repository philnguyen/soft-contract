#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "set.rkt")

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) (HashTable X Y) → (℘ X)))
(define (dom f)
  (if (hash-eq? f)
      (for/seteq: : (℘ X) ([x (in-hash-keys f)]) x)
      (for/set:   : (℘ X) ([x (in-hash-keys f)]) x)))

(: m↓ : (∀ (X Y) (HashTable X Y) (℘ X) → (HashTable X Y)))
;; Restrict map to given domain
(define (m↓ m xs)
  (cond
    [(and (immutable? m) (hash-eq? m))
     (for/hasheq : (HashTable X Y) ([(k v) m] #:when (∋ xs k))
       (values k v))]
    [(immutable? m)
     (for/hash : (HashTable X Y) ([(k v) m] #:when (∋ xs k))
       (values k v))]
    [else ; mutable
     (define m* : (HashTable X Y) (if (hash-eq? m) (make-hasheq) (make-hash)))
     (for ([(k v) m] #:when (∋ xs k))
       (hash-set! m* k v))
     m*]))

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

(: span* (∀ (X Y) ([(HashTable X (℘ Y)) (℘ X) (Y → (℘ X))] [#:eq? Boolean] . ->* . (℘ X))))
(define (span* m root f #:eq? [use-eq? #f])
  (span m root
        (if use-eq?
            (λ ([ys : (℘ Y)])
              (for/unioneq : (℘ X) ([y ys]) (f y)))
            (λ ([ys : (℘ Y)])
              (for/union : (℘ X) ([y ys]) (f y))))
        #:eq? use-eq?))

(: hash-copy/spanning (∀ (X Y) (HashTable X Y) (℘ X) (Y → (℘ X)) → (HashTable X Y)))
(define (hash-copy/spanning m xs y->xs)
  (define X-eq? (hash-eq? m))
  (define-set touched : X #:eq? X-eq? #:as-mutable-hash? #t)
  (define m* : (HashTable X Y) (if X-eq? (make-hasheq) (make-hash)))
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
  (define f : ((℘ Y) → (℘ X))
    (if (hash-eq? m)
        (λ (ys) (for/unioneq : (℘ X) ([y ys]) (y->xs y)))
        (λ (ys) (for/union : (℘ X) ([y ys]) (y->xs y)))))
  (hash-copy/spanning m xs f))

(: mk-interner (∀ (X) ([] [#:eq? Boolean] . ->* . (X → Index))))
;; Intern something as integers
(define (mk-interner #:eq? [use-eq? #f])
  (define m : (HashTable X Index) ((if use-eq? make-hasheq make-hash)))
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
