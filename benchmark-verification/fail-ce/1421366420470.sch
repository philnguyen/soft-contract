(module f racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . (lambda (x) x))]))
  (define (f g)
    (g (lambda (r) r))))
