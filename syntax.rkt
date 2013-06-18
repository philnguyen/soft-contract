#lang racket
(provide ∅ nd/c non-det non-det: if/nd match/nd)

;;;;; syntactic sugar for non-determinism

(define ∅ (set))

(define (non-det f x*)
  (cond
    [(set? x*) (for/fold ([acc ∅]) ([x x*])
                 (let ([y (f x)])
                   ((if (set? y) set-union set-add) acc y)))]
    [else (f x*)]))

(define-syntax non-det:
  (syntax-rules (<-)
    [(_ e) e]
    [(_ [p <- e] e1 ...)
     (match/nd (non-det: e) [p (non-det: e1 ...)] [_ ∅])]))

;; ∀X ≠ Set, X* = X ∪ (Setof X)
(define (nd/c p)
  (λ (x)
    (if (p x) (not (set? x)) ((set/c p) x))))

;; non-deterministic versions of conditionals
(define-syntax-rule (if/nd e e1 e2)
  (non-det (λ (x) (if x e1 e2)) e))
(define-syntax match/nd
  (syntax-rules ()
    [(_ v [p e ...] ...) (non-det (match-lambda [p e ...] ...) v)]))