#lang racket/base

(require racket/contract)
(provide (contract-out))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require)
(require "data.rkt")

(provide (struct-out posn)
         (struct-out snake)
         (struct-out world)
         )
