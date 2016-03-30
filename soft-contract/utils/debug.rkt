#lang typed/racket/base

(provide (all-defined-out))

;; Evaluate `e ...`, bind to `x ...`, run debuggings `d ...`, then return `x ...`
(define-syntax-rule (with-debugging ((x ...) e ...) d ...)
  (let-values ([(x ...) (let () e ...)])
    d ...
    (values x ...)))

(define-syntax-rule (with-debugging/off ((x ...) e ...) d ...)
  (let () e ...))

