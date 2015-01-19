(module m racket
  (provide (contract-out [f (real? real? . -> . any/c)]))
  (define (f z w)
    (expt z w)))
