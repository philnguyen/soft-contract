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

(: span (∀ (X Y) (HashTable X Y) (℘ X) (Y → (℘ X)) → (℘ X)))
(define (span m root f)
  (define-set touched : X #:eq? (hash-eq? m))
  (define (touch! [x : X]) : Void
    (unless (touched-has? x)
      (touched-add! x)
      (cond [(hash-has-key? m x)
             (set-for-each (f (hash-ref m x)) touch!)]
            [else
             (log-warning "span: warning: nothing for ~a~n" x)])))
  (set-for-each root touch!)
  touched)

(: span* (∀ (X Y) (HashTable X (℘ Y)) (℘ X) (Y → (℘ X)) → (℘ X)))
(define (span* m root f)
  (define f* : ((℘ Y) → (℘ X))
    (if (hash-eq? m)
        (λ (ys) (for/unioneq : (℘ X) ([y ys]) (f y)))
        (λ (ys) (for/union   : (℘ X) ([y ys]) (f y)))))
  (span m root f*))

(: hash-copy/spanning (∀ (X Y) (HashTable X Y) (℘ X) (Y → (℘ X)) → (HashTable X Y)))
(define (hash-copy/spanning m xs y->xs)
  (define X-eq? (hash-eq? m))
  (define-set touched : X #:eq? X-eq? #:as-mutable-hash? #t)
  (define m* : (HashTable X Y) (if X-eq? (make-hasheq) (make-hash)))
  (define (touch! [x : X]) : Void
    (unless (touched-has? x)
      (touched-add! x)
      (cond [(hash-has-key? m x)
             (define y (hash-ref m x))
             (hash-set! m* x y)
             (set-for-each (y->xs y) touch!)]
            [else
             (log-warning "hash-copy/spanning: warning: nothing for ~a~n" x)])))
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
