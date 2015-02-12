(module m racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . string?)]))
  (define (f x) x))
