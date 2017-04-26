#lang typed/racket/base

(provide (all-defined-out))

(require "pretty.rkt")

(: unique-sym (∀ (X) Symbol → (Values (X → Symbol) (Symbol → X) (→ Index))))
;; Return a bijection between `X` and Symbol.
;; No guarantee of consistency across multiple program runs.
(define (unique-sym prefix)
  (define m   : (HashTable X Symbol) (make-hash))
  (define m⁻¹ : (HashTable Symbol X) (make-hasheq))
  
  (values
   (λ (x)
     (hash-ref! m x (λ ()
                      (define s (format-symbol "~a~a" prefix (n-sub (hash-count m))))
                      (hash-set! m⁻¹ s x)
                      s)))
   (λ (s)
     (hash-ref m⁻¹ s (λ () (error 'unique-sym "No element for `~a`" s))))
   (λ () (hash-count m))))

(: make-memo (∀ (X Y) (→ (Values (X Y → X) (X → (Option Y))))))
;; Remember mapping X → Y
(define (make-memo)
  (define m : (HashTable X Y) (make-hash))
  (values
   (λ (x y) (hash-set! m x y) x)
   (λ (x) (hash-ref m x #f))))

(: make-memoeq (∀ (X Y) (→ (Values (X Y → X) (X → (Option Y))))))
;; Remember mapping X → Y
(define (make-memoeq)
  (define m : (HashTable X Y) (make-hasheq))
  (values
   (λ (x y) (hash-set! m x y) x)
   (λ (x) (hash-ref m x #f))))

(module+ test
  (require typed/rackunit)
  
  (let*-values ([(f f⁻¹ c) ((inst unique-sym String) 'x)]
                [(xs) '("foo" "bar" "qux")]
                [(is) (map f xs)])
    (for ([i is] [x xs])
      (check-equal? (f   x) i)
      (check-equal? (f⁻¹ i) x))
    (check-equal? (c) (length xs))
    (check-exn exn:fail? (λ () (f⁻¹ 'foo))))
  )
