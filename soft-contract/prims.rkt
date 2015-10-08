#lang racket/base
(require racket/math racket/contract)
(provide prims)

(define prims
  #'(;; Total unary predicates
     [#:pred number?]
     [#:pred real?]
     [#:pred integer?]
     [#:pred not]
     [#:pred boolean?]
     [#:pred string?]
     [#:pred symbol?]
     [#:pred procedure?]
     [#:pred keyword?]

     ;; Total binary predicates
     [#:pred equal? (any/c any/c)]
     
     ;; Partial predicates
     [#:pred = (number? number?)]
     [#:pred < (real? real?)]
     [#:pred <= (real? real?)]
     [#:pred > (real? real?)]
     [#:pred >= (real? real?)]
     [#:pred zero? (number?)]
     [#:pred positive? (real?)]
     [#:pred negative? (real?)]

     [#:batch (add1 sub1)
      (number? → number?)
      (real? → real?)
      (integer? → integer?)]

     [#:batch (+ - *) ; FIXME var-args
      (number? number? → number?)
      (real? real? → real?)
      (integer? integer? → integer?)]
     [/
      (number? (and/c number? (not/c zero?)) → number?)
      (real? real? → real?)]
     [expt
      (number? number? → number?)
      (real? real? → real?)
      #:other-errors
      (zero? negative?)]
     [abs
      (real? → real?)
      (integer? → integer?)
      (real? → (not/c negative?))
      ((and/c real? (not/c zero?)) → positive?)
      (zero? → zero?)]
     [#:batch (round floor ceiling)
      (real? → integer?)]
     [#:batch (log sin cos tan)
      (number? → number?)
      (real? → real?)]
     [string-length
      (string? → integer?)
      (string? → (not/c negative?))]

     [sqr
      (number? → number?)
      (real? → real?)
      (real? → (not/c negative?))
      (integer? → integer?)]

     ))
