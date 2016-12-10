#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         "def-prim.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 17.2 Unsafe Data Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
[def-alias unsafe-car car]
[def-alias unsafe-cdr cdr]
[def-alias unsafe-vector-length vector-length]
[def-alias unsafe-vector-ref vector-ref]
[def-alias unsafe-vector-set! vector-set!]
(def-prim/todo unsafe-struct-ref (any/c exact-nonnegative-integer? . -> . any/c))
(def-prim/todo unsafe-struct-set! (any/c exact-nonnegative-integer? any/c . -> . any/c))
