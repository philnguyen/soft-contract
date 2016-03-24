#lang typed/racket/base

(provide (all-defined-out))

(require "pretty.rkt")

;; Create generator for next pos/natural/negative
(define (make-neg-src)
  (let ([n : Negative-Integer -1])
    (λ () : Negative-Integer
       (begin0 n (set! n (- n 1))))))
(define (make-nat-src)
  (let ([n : Natural 0])
    (λ () : Natural
       (begin0 n (set! n (+ n 1))))))
(define (make-pos-src)
  (let ([n : Positive-Integer 1])
    (λ () : Positive-Integer
       (begin0 n (set! n (+ n 1))))))

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

(: make-memo (∀ (X Y) (→ (Values (X Y → X) (X → Y)))))
;; Remember mapping X → Y
(define (make-memo)
  (define m : (HashTable X Y) (make-hash))
  (values
   (λ (x y) (hash-set! m x y) x)
   (λ (x) (hash-ref m x))))

(: make-memoeq (∀ (X Y) (→ (Values (X Y → X) (X → Y)))))
;; Remember mapping X → Y
(define (make-memoeq)
  (define m : (HashTable X Y) (make-hasheq))
  (values
   (λ (x y) (hash-set! m x y) x)
   (λ (x) (hash-ref m x))))

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
