#lang racket
(provide ∅ nd/c non-det if/nd match/nd match? ∪)

(define ∅ (set))

;; ∀X,Y, X ≠ (Set Y), X* = X ∪ (Setof X)
(define ((nd/c p) x)
  (if (p x) (not (set? x)) ((set/c p) x)))

;; (X -> Y*) X* -> Y*
(define (non-det f x*)
  (cond
    [(set? x*) (for/fold ([acc ∅]) ([x x*]) (∪1 acc (f x)))]
    [else (f x*)]))

;; non-deterministic versions of conditionals
(define-syntax-rule (if/nd e e1 e2)
  (match/nd e [#f e2] [_ e1]))
(define-syntax-rule (match/nd v [p e ...] ...)
  (non-det (match-lambda [p e ...] ...) v))

;; Racket has this in unstable/match
(define-syntax-rule (match? v p ...)
  (match v [p #t] ... [_ #f]))

;; ∪ : X* ... -> X*
(define (∪ . xs)
  (match xs ; special cases for efficiency
    ['() ∅]
    [(list x) x]
    [_ (for/fold ([acc ∅]) ([x xs]) (∪1 acc x))]))

;; (Setof X) X* -> (Setof X)
(define (∪1 xs x*)
  ((if (set? x*) set-union set-add) xs x*))