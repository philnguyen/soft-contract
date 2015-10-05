#lang racket/base
(require racket/math racket/contract)
(provide prims)

(define prims
  #'(;; Total unary predicates
     [#:predicate number?]
     [#:predicate real?]
     [#:predicate integer?]
     [#:predicate not]
     [#:predicate boolean?]
     [#:predicate string?]
     [#:predicate symbol?]
     [#:predicate procedure?]
     [#:predicate keyword?]

     ;; Total binary predicates
     [#:predicate equal? (any/c any/c)]
     
     ;; Partial predicates
     [#:predicate = (number? number?)]
     [#:predicate < (real? real?)]
     [#:predicate <= (real? real?)]
     [#:predicate > (real? real?)]
     [#:predicate >= (real? real?)]
     [#:predicate zero? (number?)]
     [#:predicate positive? (real?)]
     [#:predicate negative? (real?)]

     [#:batch (add1 sub1)
      (number? -> number?)
      (real? -> real?)
      (integer? -> integer?)]
     [#:batch (+ - *) ; FIXME var-args
      (number? number? -> number?)
      (real? real? -> real?)
      (integer? integer? -> integer?)]
     [/
      (number? number? -> number?)
      (real? real? -> real?)
      #:errors-when
      (any/c zero?)]
     [expt
      (number? number? -> number?)
      (real? real? -> real?)
      #:errors-when
      (zero? negative?)]
     [abs
      (real? -> real?)
      (integer? -> integer?)
      (real? -> (not/c negative?))
      ((and/c real? (not/c zero?)) -> positive?)
      (zero? -> zero?)]
     [#:batch (round floor ceiling)
      (real? -> integer?)]
     [#:batch (log sin cos tan)
      (number? -> number?)
      (real? -> real?)]
     [string-length
      (string? -> integer?)
      (string? -> (not/c negative?))]

     [sqr
      (number? -> number?)
      (real? -> real?)
      (real? -> (not/c negative?))
      (integer? -> integer?)]
     ))
