(module f racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . zero?)]))
  (define (f g)
    (if (zero? (g 5))
        (* (g 5) (g 5))
        0)))
