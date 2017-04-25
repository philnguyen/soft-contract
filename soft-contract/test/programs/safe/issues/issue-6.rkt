#lang racket
(require soft-contract/fake-contract)

(define x
  (string-length "ASDF"))
x
3

(provide/contract [x integer?])
