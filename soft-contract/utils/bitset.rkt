#lang typed/racket/base

(provide make-bitset)

(: make-bitset (∀ (X) (→ (Values (Natural X → Natural)
                                 (Natural X → Boolean)
                                 ; for debugging only
                                 (Natural → (Listof X))))))
;; Create a bit-set for `X`. No guarantee about consistency across multiple program runs.
(define (make-bitset)
  (define m   : (HashTable X Natural) (make-hash))
  (define m⁻¹ : (HashTable Natural X) (make-hasheq))

  (: x->ith : X → Natural)
  (define (x->ith x)
    (hash-ref! m x (λ ()
                     (define i (hash-count m))
                     (hash-set! m⁻¹ i x)
                     i)))

  (: ith->x : Natural → X)
  (define (ith->x i)
    (hash-ref m⁻¹ i (λ () (error 'ith⁻¹ "No element indexed ~a" i))))

  (: bs->xs : Natural → (Listof X))
  (define (bs->xs bs)
    (for/list ([i (integer-length bs)] #:when (bitwise-bit-set? bs i))
      (ith->x i)))

  (: add : Natural X → Natural)
  (define (add bs x)
    (bitwise-ior bs (arithmetic-shift 1 (x->ith x))))

  (: has? : Natural X → Boolean)
  (define (has? bs x)
    (bitwise-bit-set? bs (x->ith x)))
  
  (values add has? bs->xs))


(module+ test
  (require typed/rackunit racket/set)

  (let-values ([(add has? bs->xs) ((inst make-bitset Symbol))])
    (define n (add (add (add 0 'foo) 'bar) 'qux))
    (check-true (has? n 'foo))
    (check-true (has? n 'bar))
    (check-true (has? n 'qux))
    (check-false (has? n 'nope))
    (check-equal? (list->set (bs->xs n)) {set 'foo 'bar 'qux}))
  )
