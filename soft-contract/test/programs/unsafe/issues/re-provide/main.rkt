#lang racket/base

(module require/contracts racket/base
  (require racket/contract
           "posn.rkt")
  (provide (contract-out (struct posn ()))))

(require 'require/contracts)
(posn 1)
