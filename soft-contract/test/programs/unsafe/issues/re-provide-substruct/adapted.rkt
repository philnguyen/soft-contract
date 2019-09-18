#lang racket/base

(module require/contracts racket/base
  (require racket/contract
           "structs.rkt")
  (provide (contract-out (struct Stx ((label any/c))))
           (contract-out (struct (exp Stx) ((label any/c))))))

(require 'require/contracts)
(provide (struct-out Stx)
         (struct-out exp))

;; make sure reached
(/ 1 0)
