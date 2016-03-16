#lang typed/racket/base

(provide match/nd:)

(require racket/match racket/set "set.rkt")

;; non-deterministic match. The types is to make it less awkard in pattern matching
(define-syntax match/nd:
  (syntax-rules (→)
    [(_ (α → β) v [p e ...] ...)
     (let ()
       (define x v)
       (define f : (α → (U β (℘ β)))
         (match-lambda [p e ...] ... [x (error 'match/nd "unmatched: ~a" x)]))
       (cond
         [(set? x) (for/fold ([acc : (℘ β) ∅]) ([xᵢ x])
                     (define y (f xᵢ))
                     (if (set? y) (set-union acc y) (set-add acc y)))]
         [else (f x)]))]
    [(_ #:tag tag (α → β) v [p e ...] ...)
     (match/nd: (α → β) v [p e ...] ... [x (error 'tag "unmatched: ~a" x)])]))
