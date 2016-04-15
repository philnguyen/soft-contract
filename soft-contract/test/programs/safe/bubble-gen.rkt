#lang racket/base
(require soft-contract/fake-contract)

(define (bubble-sort vec)
  (when (for/fold ([swapped? #f]) ([i (in-range (sub1 (vector-length vec)))])
          (let ([a (vector-ref vec i)]
                [b (vector-ref vec (+ 1 i))])
            (if (a . > . b)
                (begin
                  (vector-set! vec i b)
                  (vector-set! vec (+ 1 i) a)
                  #t)
                swapped?)))
    (bubble-sort vec)))

(provide/contract
 [bubble-sort ((vectorof integer?) . -> . void?)])
