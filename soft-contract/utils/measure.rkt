#lang typed/racket/base

(provide with-measuring with-measuring/off highest-calls highest-time)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/list)

(define total-time  : (HashTable Any Integer) (make-hash))
(define total-calls : (HashTable Any Integer) (make-hash))

(define mk-0 (λ () 0))

(define-syntax with-measuring
  (syntax-parser
    [(_ t e ...)
     #'(let ([vt t]
             [t₀ (current-milliseconds)])
         (begin0
             (let () e ...)
           (let ([δt (- (current-milliseconds) t₀)])
             (hash-update! total-calls vt add1 mk-0)
             (hash-update! total-time  vt (λ ([T : Integer]) (+ T δt)) mk-0))))]))

(define-syntax with-measuring/off
  (syntax-parser
    [(_ t e ...)
     #'(let () e ...)]))

(: highest-calls ([] [Natural] . ->* . (Listof (Pairof Any Integer))))
(define (highest-calls [num 1]) (table-max total-calls num))

(: highest-time ([] [Natural] . ->* . (Listof (Pairof Any Integer))))
(define (highest-time [num 1]) (table-max total-time num))

(: table-max ((HashTable Any Integer) Natural → (Listof (Pairof Any Integer))))
(define (table-max m num)
  (define sorted-pairs
    (sort
     (hash->list m)
     (λ ([p₁ : (Pairof Any Integer)] [p₂ : (Pairof Any Integer)])
       (> (cdr p₁) (cdr p₂)))))
  (take sorted-pairs (min (hash-count m) num)))
