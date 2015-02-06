(module m racket
  (provide (contract-out [f ((and/c procedure? number?) . -> . string?)]))
  (define (f x) x))
