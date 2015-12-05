#lang typed/racket/base

(provide (all-defined-out))

(require racket/match)

(define-type -R (U '✓ 'X '?))

(: not-R : -R → -R)
;; Negate provability result
(define not-R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

;; Take the first definite result
(define-syntax first-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...)
     (match R₁ ['? (first-R R ...)] [ans ans])]))

(define (decide-R [x : Boolean]) : -R (if x '✓ 'X))
