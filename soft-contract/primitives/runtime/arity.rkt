#lang typed/racket/base

(provide Arity update-arity! get-arity)

(require "../../utils/def.rkt")
(require/typed racket/function
  [arity-includes? (Arity Arity → Boolean)]
  [normalize-arity ((Listof Arity) → Arity)])

;; The kind of arities that we care about, for now
(Arity . ::= . Natural arity-at-least (Listof (U Natural arity-at-least)))

(define arity-table : (HashTable Symbol Arity) (make-hasheq))

(: update-arity! : Symbol Arity → Void)
(define (update-arity! o a)
  (cond [(hash-ref arity-table o #f) =>
         (λ ([a₀ : Arity])
           (unless (arity-includes? a₀ a)
             (hash-set! arity-table o (normalize-arity (list a₀ a)))))]
        [else
         (hash-set! arity-table o a)]))

(: get-arity : Symbol → Arity)
(define (get-arity o) (hash-ref arity-table o (λ () (error 'get-arity "nothing for ~a" o))))
