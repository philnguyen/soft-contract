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
    [(immutable? m)
     (for/fold ([m* : (HashTable X Y) (hash-copy-clear m)])
               ([(k v) (in-hash m)] #:when (∋ xs k))
       (hash-set m* k v))]
    [else
     (define m* : (HashTable X Y) (hash-copy-clear m))
     (for ([(k v) (in-hash m)] #:when (∋ xs k))
       (hash-set! m* k v))
     m*]))

(: map/hash (∀ (X Y Z) (Y → Z) (HashTable X Y) → (HashTable X Z)))
(define (map/hash f m)
  (for/fold ([m* : (HashTable X Z) (if (hash-eq? m) (hasheq) (hash))])
            ([(x y) (in-hash m)])
    (hash-set m* x (f y))))

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
  (span m root (mk-set-spanner f #:eq? (hash-eq? m))))

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
  (hash-copy/spanning m xs (mk-set-spanner y->xs #:eq? (hash-eq? m))))

(: hash-set-once! (∀ (X Y) (HashTable X Y) X Y → Void))
(define (hash-set-once! m x v)
  (cond [(hash-has-key? m x)
         (error 'hash-set-once! "key already exists: ~a" x)]
        [else (hash-set! m x v)]))

(: map-has? (∀ (X Y) (HashTable X (℘ Y)) X Y → Boolean))
(define (map-has? m x y)
  (cond [(hash-ref m x #f) => (λ ([ys : (℘ Y)]) (∋ ys y))]
        [else #f]))

(: map-add! (∀ (X Y) (HashTable X (℘ Y)) X Y #:eq? Boolean → Void))
(define (map-add! m x y #:eq? use-eq?)
  (define mk-∅ (if use-eq? →∅eq →∅))
  (hash-update! m x (λ ([ys : (℘ Y)]) (set-add ys y)) mk-∅))

(: map-equal?/spanning-root
   (∀ (X Y) (HashTable X (℘ Y)) (HashTable X (℘ Y)) (℘ X) (Y → (℘ X)) → Boolean))
;; CHeck if 2 multimaps are equal up to the domain spanned by given set
(define (map-equal?/spanning-root m₁ m₂ xs span)
  (define-set seen : X #:eq? (hash-eq? m₁) #:as-mutable-hash? #t)
  (let loop : Boolean ([xs : (℘ X) xs])
       (for/and : Boolean ([x (in-set xs)])
         (cond [(seen-has? x) #t]
               [else
                (seen-add! x)
                (define ys₁ (hash-ref m₁ x →∅))
                (define ys₂ (hash-ref m₂ x →∅))
                (and (equal? ys₁ ys₂)
                     (for/and : Boolean ([y (in-set ys₁)])
                       (loop (span y))))]))))

(: mk-set-spanner (∀ (X Y) ([(X → (℘ Y))] [#:eq? Boolean] . ->* . ((℘ X) → (℘ Y)))))
(define (mk-set-spanner f #:eq? [use-eq? #f])
  (cond [use-eq? (λ (xs) (for/unioneq : (℘ Y) ([x (in-set xs)]) (f x)))]
        [else    (λ (xs) (for/union   : (℘ Y) ([x (in-set xs)]) (f x)))]))

;; For debugging
(: large-ones (∀ (X Y) (HashTable X (℘ Y)) Natural → (HashTable X (℘ Y))))
(define (large-ones m n)
  (for/fold ([m* : (HashTable X (℘ Y)) m])
            ([(k vs) (in-hash m)] #:unless (>= (set-count vs) n))
    (hash-remove m* k)))
