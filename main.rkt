#lang racket/base
(require racket/match racket/port
         "utils.rkt"
         (only-in "check.rkt" feedback)
         (only-in redex/reduction-semantics variable-not-in)
         (for-syntax racket/base racket/match))
(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         #%app #%datum #%top
         read read-syntax)

(define-syntax-rule (module-begin m ...)
  (#%module-begin (feedback/massage '(m ...))))

(define-syntax-rule (top-interaction . x)
  (#%top-interaction . (feedback/massage 'x)))

#;(define-syntax-rule (top-interaction . e)
  (#%top-interaction . (begin #;(printf "Run Top:~n~a~n" (massage-top 'e))
                              (feedback (massage-top 'e)))))

(define (feedback/massage x)
  #;(printf "Prog:~n~a~n" (pretty (massage x)))
  (feedback (massage x)))

;; Havoc each exported identifier
(define (massage p)
  (match p
    [(list (and modl `(module ,m racket ,dss ...)) ...)
     (define names
       (for*/fold ([acc '()]) ([ds dss] [d ds])
         (append #|bad but not too bad|# (collect-names d) acc)))
     `(,@modl
       (require ,@(for/list ([mᵢ m]) `(quote ,mᵢ)))
       (amb ,@(for/list ([x names]) `(• ,x))))]
    [(list (and modl `(module ,_ racket ,_ ...)) ... `(require ,x ...) e)
     p
     #;(define main (variable-not-in modl 'main))
     #;(massage
      `(,@modl
        (module ,main racket
          (provide/contract [,main any/c])
          (require ,@(for/list ([xᵢ x]) `(submod ".." ,(cadr xᵢ))))
          (define (,main) ,e))))]
    [(list (and modl `(module ,_ racket ,_ ...)) ... e)
     (massage `(,@modl (require) ,e))]
    [(and m `(module ,_ racket ,_ ...)) (massage (list m))]
    [e (list e)]))

(define collect-names
  (match-lambda
   [`(provide/contract [,x ,_] ...) x]
   [_ '()]))
