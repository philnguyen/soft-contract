#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         "def-prim.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.6 Structure Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-pred struct-type?)
