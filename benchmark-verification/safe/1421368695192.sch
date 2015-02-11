(module m racket
  (provide (contract-out [f ((and/c integer? string?) . -> . string?)]))
  (define (f x) 5))
