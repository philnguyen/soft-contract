#lang racket/base
(require racket/contract)
(let ([r (make-vector 1 (contract any/c 41 'g9983 'NEG))])
  (if (= (contract exact-integer? (vector-ref r 0) 'g9984 'NEG) 8)
      (vector-set! r 0 (contract any/c #t 'g9985 'NEG))
      (vector-set! r 0 (contract any/c #f 'g9986 'NEG)))
  (contract boolean? (vector-ref r 0) 'g9987 'NEG))
