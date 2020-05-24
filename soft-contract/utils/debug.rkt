#lang typed/racket/base

(provide with-debugging
         with-debugging/off
         (rename-out [-assert assert]))
(require syntax/parse/define
         (for-syntax racket/base))

;; Evaluate `e ...`, bind to `x ...`, run debuggings `d ...`, then return `x ...`
(define-simple-macro (with-debugging ((x:id ...) e ...) d ...)
  (let-values ([(x ...) (let () e ...)])
    d ...
    (values x ...)))

(define-simple-macro (with-debugging/off ((x:id ...) e ...) d ...)
  (let () e ...))

(begin-for-syntax
  (define (wrap stx e)
    (with-syntax ([src (syntax-source stx)]
                  [line (syntax-line stx)]
                  [col (syntax-column stx)])
      #`(with-handlers ([exn? (λ _
                                (error 'assert "~a fails at ~a:~a:~a" '#,e src line col))])
          #,e))))

(define-syntax-parser -assert
  [(~and stx (_ x  )) (wrap #'stx #'(assert x  ))]
  [(~and stx (_ x p)) (wrap #'stx #'(assert x p))])
