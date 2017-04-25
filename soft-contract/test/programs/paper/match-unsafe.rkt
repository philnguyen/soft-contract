#lang racket

(provide/contract
 [f ((or/c (cons/c real? string?) string?) . -> . real?)])

(define (f x)
  (match x
    [(cons r s) #:when (<= r -1) (string-length s)]
    [(cons r s) (/ (string-length s) r)]
    [_ (string-length x)]))
