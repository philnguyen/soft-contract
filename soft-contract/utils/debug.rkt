#lang typed/racket/base

(provide (all-defined-out))
(require syntax/parse/define)

;; Evaluate `e ...`, bind to `x ...`, run debuggings `d ...`, then return `x ...`
(define-simple-macro (with-debugging ((x:id ...) e ...) d ...)
  (let-values ([(x ...) (let () e ...)])
    d ...
    (values x ...)))

(define-simple-macro (with-debugging/off ((x:id ...) e ...) d ...)
  (let () e ...))

