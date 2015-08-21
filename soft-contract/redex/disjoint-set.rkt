#lang typed/racket/base
(provide Forestof entry entry? entry-parent
         forest forest-same? forest-add forest-find forest-union
         forest-keys forest-count forest-count-partitions)
(require racket/set)

;; A (Forestof X) is a map from each value X to its representative element and a rank
;; TODO: I only want `parent` to be mutable but TR...
(define-type (Forestof X) (HashTable X (entry X)))
(struct (X) entry ([rank : Natural] [parent : X]) #:transparent #:mutable)

(: forest : (∀ (X) X * → (Forestof X)))
;; Create a new forest where each value belongs to its own set
(define (forest . xs)
  (for/hash : (Forestof X) ([x xs]) (values x (entry 0 x))))

(: forest-keys : (∀ (X) (Forestof X) → (Listof X)))
;; Return the list of values in forest
(define (forest-keys f) (hash-keys f))

(: forest-count : (∀ (X) (Forestof X) → Natural))
(define (forest-count f) (hash-count f))

(: forest-count-partitions : (∀ (X) (Forestof X) → Natural))
;; Count the number of partitions in forest
(define (forest-count-partitions f)
  (set-count
   (for/fold ([s : (Setof X) (set)]) ([e (in-hash-values f)])
     (set-add s (entry-parent e)))))

(: forest-add : (∀ (X) (Forestof X) X * → (Forestof X)))
;; Add new values to forest. Raise error if any value is already in there.
(define (forest-add f . xs)
  (for/fold ([f : (Forestof X) f]) ([x xs])
    (cond
      [(hash-has-key? f x) (error 'forest-add "value ~a is already in forest" x)]
      [else (hash-set f x (entry 0 x))])))

(: forest-find : (∀ (X) (Forestof X) X → X))
;; Return this value's representative element in the forest.
;; This operation performs path compression internally, but should be "functional" from outside
(define (forest-find f x)
  (define e (hash-ref f x))
  (define p (entry-parent e))
  (cond
    [(equal? p x) p]
    [else
     (define p* (forest-find f p))
     (set-entry-parent! e p*)
     p*]))

(: forest-same? : (∀ (X) (Forestof X) X X → Boolean))
;; Check whether 2 elements belong to the same set
(define (forest-same? f x y)
  (equal? (forest-find f x) (forest-find f y)))

(: forest-union : (∀ (X) (Forestof X) X X * → (Forestof X)))
;; Merge all given elements into 1 set
(define (forest-union f x . xs)
  (for/fold ([f : (Forestof X) f]) ([z xs])
    (forest-union1 f x z)))

(: forest-union1 : (∀ (X) (Forestof X) X X → (Forestof X)))
;; Merge 2 elements into 1 set
(define (forest-union1 f x y)
  (define x-root (forest-find f x))
  (define y-root (forest-find f y))
  (cond
    [(equal? x-root y-root) f]
    [else
     (define x-rank (entry-rank (hash-ref f x)))
     (define y-rank (entry-rank (hash-ref f y)))
     (cond
       [(< x-rank y-rank) (with-parent f x-root y-root)]
       [(> x-rank y-rank) (with-parent f y-root x-root)]
       [else (inc-rank (with-parent f y-root x-root) x-root)])]))

(: inc-rank : (∀ (X) (Forestof X) X → (Forestof X)))
;; Increase the rank of the given node by 1
(define (inc-rank f x)
  (hash-update f x (λ ([e : (entry X)])
                     (entry (+ 1 (entry-rank e)) (entry-parent e)))))

(: with-parent : (∀ (X) (Forestof X) X X → (Forestof X)))
;; Update the node's parent
(define (with-parent f x y)
  (hash-update f x (λ ([e : (entry X)])
                     (entry (entry-rank e) y))))

;; Examples
(define f (forest 1 2 3 4 5 6))
(define g (forest-add f 7 8))
(define h (forest-union (forest-union g 1 3 5 7) 2 4 6 8))
