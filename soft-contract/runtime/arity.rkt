#lang typed/racket/base

(provide V-arity formals-arity guard-arity simple-arity?)

(require racket/match
         "../utils/list.rkt"
         "../ast/definition.rkt"
         "definition.rkt")

(require/typed/provide racket/function
  [arity-includes? (Arity Arity → Boolean)])
(require/typed "../primitives/declarations.rkt"
  [(prims prims:prims) (Listof Any)])

(define formals-arity : (-formals → Arity)
  (match-lambda
    [(-varargs init _) (arity-at-least (length init))]
    [(? list? xs) (length xs)]))

(define guard-arity : (-=>_ → Arity)
  (match-lambda
    [(-=> αs _) (length αs)]
    [(-=>i _ β)
     (match β
       [(-λ xs _) (formals-arity xs)]
       [_ (error 'guard-arity "unhandled")])]))

(: V-arity : -V → (Option Arity))
;; Return given value's arity, or `#f` if it's not a procedure
(define V-arity
  (let ()
    (define arity-table
      (for/fold ([m : (HashTable Symbol Arity) (hasheq)]) ([dec prims:prims])
        (match dec
          [`(#:pred ,(? symbol? s))
           (hash-set m s 1)]
          [`(#:pred ,(? symbol? s) (,xs ...))
           (hash-set m s (length xs))]
          [`(#:batch (,ss ...) (,xs ... . -> . ,_) ,_ ...)
           (define n (length xs))
           (for/fold ([m : (HashTable Symbol Arity) m]) ([s ss])
             (hash-set m (assert s symbol?) n))]
          [`(#:batch (,ss ...) (,xs #:rest ,_ . ->* . ,_) ,_ ...)
           (define n (arity-at-least (length (assert xs list?))))
           (for/fold ([m : (HashTable Symbol Arity) m]) ([s ss])
             (hash-set m (assert s symbol?) n))]
          [`(,(? symbol? s) (,xs ... . -> . ,_) ,_ ...)
           (hash-set m s (length xs))]
          [`(,(? symbol? s) (,(? list? xs) #:rest ,_ . ->* . ,_) ,_ ...)
           (hash-set m s (arity-at-least (length xs)))]
          [_ m])))

    (match-lambda
      [(-Clo xs _ _ _) (formals-arity xs)]
      [(-Case-Clo clauses _ _)
       (remove-duplicates
        (for/list : (Listof Natural) ([clause clauses])
          (match-define (cons xs _) clause)
          (length xs)))]
      [(or (-And/C #t _ _) (-Or/C #t _ _) (? -Not/C?) (-St/C #t _ _)) 1]
      [(-Ar guard _ _) (guard-arity guard)]
      [(? -st-p?) 1]
      [(-st-mk (-struct-info _ n _)) n]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? o) (hash-ref arity-table o)]
      [(-● _) #f]
      [V
       (printf "Warning: call `V-arity` on an obviously non-procedure ~a" (show-V V))
       #f])))

(define (simple-arity? x)
  (or (exact-nonnegative-integer? x) (arity-at-least? x)))
