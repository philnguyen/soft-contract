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

(define-syntax (with-memo stx)
  (syntax-parse stx
    #:literals (→ ->)
    [(_ (X (~or → ->) Y) f)
     #`(let ([m : (HashTable X Y) (make-hash)])
         (λ ([x : X]) : Y
            (hash-ref! m x (λ () ((ann f (X → Y)) x)))))]))

(define-syntax (with-memoeq stx)
  (syntax-parse stx
    #:literals (→ ->)
    [(_ (X (~or → ->) Y) f)
     #`(let ([m : (HashTable X Y) (make-hasheq)])
         (λ ([x : X]) : Y
            (hash-ref! m x (λ () ((ann f (X → Y)) x)))))]))
