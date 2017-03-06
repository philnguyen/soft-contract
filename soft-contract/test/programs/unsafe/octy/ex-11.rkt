#lang racket
(require soft-contract/fake-contract)

(define (f g p)
  (if #|HERE|# (number? (car p)) (g p) 'no))

(provide/contract
 [f (((cons/c number? number?) . -> . symbol?) cons? . -> . symbol?)])
