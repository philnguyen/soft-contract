#lang racket

(module sub racket/base
  (require racket/contract
           "data.rkt")
  (provide
   (contract-out
    (struct posn ([x real?])))))

(require 'sub)

(define x 42)

(provide
 [struct-out posn]
 (contract-out ; make sure it's reached
  [x string?]))
