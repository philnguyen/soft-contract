(module m racket
  (provide (contract-out [f ((and/c procedure? number?) . -> . any/c)]))
  (define (f g) 5))
