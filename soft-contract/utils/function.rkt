#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base racket/syntax syntax/parse))

(: fix : (∀ (X) (X → X) X → X))
;; Compute `f`'s fixpoint starting from `x`
(define (fix f x)
  (define x* (f x))
  (if (equal? x x*) x (fix f x*)))

(define-syntax-rule (apply/values f x)
  (call-with-values (λ () x) f))

(define-syntax define/memo
  (syntax-rules (:)
    [(_ (f [x : X]) : Y e ...)
     (define f : (X → Y)
       (let ([m : (HashTable X Y) (make-hash)])
         (λ ([x : X])
           (hash-ref! m x (λ () : Y e ...)))))]
    [(_ (f [x : X] ...) : Y e ...)
     (define f : (X ... → Y)
       (let ([m : (HashTable (List X ...) Y) (make-hash)])
         (λ ([x : X] ...)
           (hash-ref! m (list x ...) (λ () : Y e ...)))))]))

(define-syntax define/memoeq
  (syntax-rules (:)
    [(_ (f [x : X]) : Y e ...)
     (define f : (X → Y)
       (let ([m : (HashTable X Y) (make-hasheq)])
         (λ ([x : X])
           (hash-ref! m x (λ () : Y e ...)))))]))
