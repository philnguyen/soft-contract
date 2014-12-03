#lang racket/base
(require racket/match
         (only-in "check.rkt" feedback)
         (only-in redex/reduction-semantics variable-not-in)
         (for-syntax racket/base racket/match))
(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         #%app #%datum #%top
         read read-syntax)

(define-syntax-rule (module-begin m ...)
  (#%module-begin (begin #;(printf "Run Program:~n~a~n" (massage-prog '(m ...)))
                         (feedback/massage '(m ...)))))

(define-syntax-rule (top-interaction . x)
  (#%top-interaction . (feedback/massage 'x)))

#;(define-syntax-rule (top-interaction . e)
  (#%top-interaction . (begin #;(printf "Run Top:~n~a~n" (massage-top 'e))
                              (feedback (massage-top 'e)))))

(define (feedback/massage x)
  #;(printf "Prog:~n~a~n" x)
  (feedback (massage x)))

;; Havoc each exported identifier
(define (massage p)
  (match p
    [(list (and modl `(module ,m ,dss ...)) ...)
     (define names
       (for*/fold ([acc '()]) ([ds dss] [d ds])
         (append #|bad but not too bad|# (collect-names d) acc)))
     `(,@modl
       (require ,@m)
       (amb ,@(for/list ([x names]) `(• ,x))))]
    [(list (and modl `(module ,_ ...)) ... `(require ,x ...) e)
     (define main (variable-not-in modl 'main))
     (massage `(,@modl (module ,main (provide [,main any/c]) (require ,@x) (define (,main) ,e))))]
    [(list (and modl `(module ,_ ...)) ... e)
     (massage `(,@modl (require) ,e))]
    [(and m `(module ,_ ...)) (massage (list m))]
    [e (list e)]))

(define collect-names
  (match-lambda
   [`(provide [,x ,_] ...) x]
   [_ '()]))
