#lang typed/racket/base

(provide (all-defined-out))

(require racket/match "../ast/definition.rkt" "../utils/def.rkt" "val.rkt" "env.rkt" "path-inv.rkt")
(require/typed "../primitives/declarations.rkt"
 [(prims prims:prims) (Listof Any)])

;; Use Racket's representation of arity to make it a bit easier to manipulate things in proof rules.
;; In the object language, it's the executed language's lists, so more awkward.
(define-type Arity (U Natural arity-at-least (Listof (U Natural arity-at-least))))

(require/typed/provide racket/function
  [arity-includes? (Arity Arity → Boolean)])

(define (simple-arity? x)
  (or (exact-nonnegative-integer? x) (arity-at-least? x)))

(: -procedure-arity : -V → (Option Arity))
;; Return given value's arity
(define -procedure-arity
  (let ()
    
    (define (-formals-arity [xs : -formals]) : Arity
      (cond
        [(-varargs? xs) (arity-at-least (length (-varargs-init xs)))]
        [else (length xs)]))

    (define (-guard-arity [guard : -=>i]) : Arity
      (match-define (-=>i doms rst _ _ _) guard)
      (define n (length doms))
      (if rst (arity-at-least n) n))

    (define arity-table
      (for/fold ([m : (HashTable Symbol Arity) (hasheq)]) ([dec prims:prims])
        (match dec
          [`(#:pred ,(? symbol? s)) (hash-set m s 1)]
          [`(#:pred ,(? symbol? s) (,xs ...)) (hash-set m s (length xs))]
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
          [`(,(? symbol? s) (,xs #:rest ,_ . ->* . ,_) ,_ ...)
           (hash-set m s (arity-at-least (length (assert xs list?))))]
          [_ m])))

    (match-lambda
      [(or (-Clo xs _ _ _) (-Clo* xs _ _)) (-formals-arity (assert xs))]
      [(or (-And/C #t _ _) (-Or/C #t _ _) (? -Not/C?) (-St/C #t _ _)) 1]
      [(-Ar guard _ _) (-guard-arity guard)]
      [(? -st-p?) 1]
      [(-st-mk (-struct-info _ n _)) n]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? s) (hash-ref arity-table s)]
      [(-●) #f]
      [V (error '-procedure-arity "called on a non-procedure ~a" (show-V V))])))

(define (-Arity-Includes/C [n : (U Natural arity-at-least)])
  (-Clo '(x) (-@ 'arity-includes? (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤))
