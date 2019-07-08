#lang racket/base
(require racket/contract)
(provide sqrt
         (contract-out
          [add1 (integer? . -> . integer?)]))
