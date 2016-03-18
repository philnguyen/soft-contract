#lang typed/racket/base

(provide unique-nat unique-sym)

(require "pretty.rkt")

(: unique-nat (∀ (X) ([] [#:hacked-warning (Option Natural)]
                      . ->* .
                      (Values (X → Natural) (Natural → X) (→ Natural)))))
;; Return a bijection between `X` and ℤ.
;; No guarantee of consistency across multiple program runs.
(define (unique-nat #:hacked-warning [N #f])
  (define m   : (HashTable X Natural) (make-hash))
  (define m⁻¹ : (HashTable Natural X) (make-hasheq))

  (values
   (λ (x)
     (hash-ref! m x (λ ()
                      (define i (hash-count m))
                      (hash-set! m⁻¹ i x)
                      (when (and N (> i N))
                        (printf "Warning: unexpectedly more than ~a~n" N))
                      i)))
   (λ (i)
     (hash-ref m⁻¹ i (λ () (error 'unique-nat "No element for index `~a`" i))))
   (λ () (hash-count m))))

(: unique-sym (∀ (X) ([Symbol] [#:transform-index (Natural → Any)]
                      . ->* .
                      (Values (X → Symbol) (Symbol → X) (→ Natural)))))
;; Return a bijection between `X` and Symbol.
;; No guarantee of consistency across multiple program runs.
(define (unique-sym prefix #:transform-index [f n-sub])
  (define m   : (HashTable X Symbol) (make-hash))
  (define m⁻¹ : (HashTable Symbol X) (make-hasheq))
  
  (values
   (λ (x)
     (hash-ref! m x (λ ()
                      (define s (format-symbol "~a~a" prefix (f (hash-count m))))
                      (hash-set! m⁻¹ s x)
                      s)))
   (λ (s)
     (hash-ref m⁻¹ s (λ () (error 'unique-sym "No element for `~a`" s))))
   (λ () (hash-count m))))

(module+ test
  (require typed/rackunit)
  
  (let*-values ([(f f⁻¹ c) ((inst unique-nat Symbol))]
                [(xs) '(foo bar qux)]
                [(is) (map f xs)])
    (for ([i : Natural is] [x xs])
      (check-equal? (f   x) i)
      (check-equal? (f⁻¹ i) x))
    (check-equal? (c) (length xs))
    (check-exn exn:fail? (λ () (f⁻¹ 3))))

  (let*-values ([(f f⁻¹ c) ((inst unique-sym String) 'x)]
                [(xs) '("foo" "bar" "qux")]
                [(is) (map f xs)])
    (for ([i is] [x xs])
      (check-equal? (f   x) i)
      (check-equal? (f⁻¹ i) x))
    (check-equal? (c) (length xs))
    (check-exn exn:fail? (λ () (f⁻¹ 'foo))))
  )
