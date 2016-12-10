#lang typed/racket/base

(provide (all-defined-out))

(require "../utils/def.rkt")

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
     (let ([ans R₁])
       (case ans
         ['? (first-R R ...)]
         [else ans]))]))

(: boolean->R : Boolean → (U '✓ '✗))
(define (boolean->R x) (if x '✓ '✗))
