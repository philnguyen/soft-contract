#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/bool
         set-extras)

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) (HashTable X Y) → (℘ X)))
(define (dom f)
  (if (hash-eq? f)
      (for/seteq: : (℘ X) ([x (in-hash-keys f)]) x)
      (for/set:   : (℘ X) ([x (in-hash-keys f)]) x)))

(: m↓ : (∀ (X Y) (Immutable-HashTable X Y) (℘ X) → (Immutable-HashTable X Y)))
;; Restrict map to given domain
(define (m↓ m xs)
  (for/fold ([m* : (Immutable-HashTable X Y) m])
            ([k (in-hash-keys m)] #:unless (∋ xs k))
    (hash-remove m* k)))

(: map/hash (∀ (X Y Z) (Y → Z) (Immutable-HashTable X Y) → (Immutable-HashTable X Z)))
(define (map/hash f m)
  (for/fold ([m* : (Immutable-HashTable X Z) (if (hash-eq? m) (hasheq) (hash))])
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
  (define mk (if use-eq? mk-∅eq mk-∅))
  (hash-update! m x (λ ([ys : (℘ Y)]) (set-add ys y)) mk))

(: map-equal?/spanning-root
   (∀ (X Y) ([(HashTable X (℘ Y)) (HashTable X (℘ Y)) (℘ X) (Y → (℘ X))] [(X → Boolean)] . ->* . Boolean)))
;; CHeck if 2 multimaps are equal up to the domain spanned by given set
(define (map-equal?/spanning-root m₁ m₂ xs span [check? (λ _ #t)])
  (define-set seen : X #:eq? (hash-eq? m₁) #:as-mutable-hash? #t)
  (let loop : Boolean ([xs : (℘ X) xs])
       (for/and : Boolean ([x (in-set xs)])
         (cond [(seen-has? x) #t]
               [else
                (seen-add! x)
                (define ys₁ (hash-ref m₁ x mk-∅))
                (define ys₂ (hash-ref m₂ x mk-∅))
                (and ((check? x) . implies . (equal? ys₁ ys₂))
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

(: count-max : (∀ (X Y) ((HashTable X (℘ Y)) → Index)))
(define (count-max m)
  (apply max 0 ((inst map Index (℘ Any)) set-count (hash-values m))))
