#lang racket/base
(require racket/contract)

(let* ([r0 (make-vector 1 1)]
       [r1 (contract (vectorof any/c) r0 'g9963 'NEG)]
       [r2 (contract (vectorof string?) r1 'g9964 'NEG)]
       [r3 (contract any/c r2 'g9965 'NEG)])
  (vector-set!
   (contract (vectorof any/c) r3 'g9966 'NEG)
   0
   (contract any/c 42 'g9967 'NEG))
  (contract
   exact-integer?
   (vector-ref (contract (vectorof any/c) r3 'g9969 'NEG) 0)
   'g9968
   'NEG))
