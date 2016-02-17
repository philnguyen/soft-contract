#lang typed/racket/base

(provide (all-defined-out))

(require racket/match "../utils/def.rkt")

(-R . ::= . '✓ '✗ '?)

(: not-R : -R → -R)
;; Negate provability result
(define (not-R R)
  (case R [(✓) '✗] [(✗) '✓] [else '?]))

;; Take the first definite result
(define-syntax first-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...)
     (match R₁ ['? (first-R R ...)] [ans ans])]))

(define (decide-R [x : Boolean]) : -R (if x '✓ '✗))
