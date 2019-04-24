#lang typed/racket/base

(provide make-union-find)

(require racket/set
         racket/match)

(: make-union-find (∀ (X) (→ (Values (X X → Void) (X → X)))))
;; Given set of all elements, return functions for:
;; - Marking two elements as belonging to the same partition
;; - Finding a representative element, given one
(define (make-union-find)
  (define parent : (Mutable-HashTable X X) (make-hash))
  (define rank : (Mutable-HashTable X Integer) (make-hash))
  (define (parent-of [x : X]) (hash-ref parent x (λ () x)))
  (define (rank-of [x : X]) (hash-ref rank x (λ () 0)))

  (: union! : X X → Void)
  ;; Mark `x` and `y` as belonging in the same partition
  (define (union! x y)
    (define x* (find x))
    (define y* (find y))
    (unless (equal? x* y*)
      (define-values (x:root x:root:rank y:root y:root:rank)
        (let ([x*:rank (rank-of x*)]
              [y*:rank (rank-of y*)])
          (if (< x*:rank y*:rank)
              (values y* y*:rank x* x*:rank)
              (values x* x*:rank y* y*:rank))))
      (hash-set! parent y:root x:root)
      (when (= x:root:rank y:root:rank)
        (hash-set! rank x:root (add1 x:root:rank)))))

  (: find : X → X)
  ;; Return the element that represents `x`
  (define (find x)
    (match (parent-of x)
      [(== x) x]
      [(app find x*) (hash-set! parent x x*)
                     x*]))

  (values union! find))
