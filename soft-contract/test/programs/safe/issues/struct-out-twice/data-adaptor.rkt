#lang racket

(module sub racket/base
  (require racket/contract
           "data.rkt")
  (provide
   (contract-out
    (struct posn ([x real?])))))

(require 'sub)

(provide
 [struct-out posn])
