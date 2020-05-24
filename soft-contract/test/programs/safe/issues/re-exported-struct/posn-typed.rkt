#lang racket/base

(require racket/contract
         "posn-untyped.rkt")

(provide
 (contract-out
  [struct posn-3d ([x real?] [y real?] [z real?])]
  [struct posn-2d ([x real?] [y real?])]))
