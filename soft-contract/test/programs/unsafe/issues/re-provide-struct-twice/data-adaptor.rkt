#lang racket/base

(module require/contracts racket/base
  (require racket/contract
           "data.rkt")
  (provide (contract-out (struct foo ()))))

(require racket/contract
         require-typed-check
         (prefix-in -: (only-in 'require/contracts foo?))
         (except-in 'require/contracts foo?))

(provide (struct-out foo))
