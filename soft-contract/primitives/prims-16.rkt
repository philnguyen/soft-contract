#lang typed/racket/base

(provide (all-defined-out))
(require racket/contract
         "def-prim.rkt")

(def-prim make-weak-box (any/c . -> . weak-box?))
(def-prim weak-box-value (weak-box? . -> . any/c)) ; FIXME uses
(def-pred weak-box?)
