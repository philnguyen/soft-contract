(module f racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . (</c 10))]))
  (define (f g)
    (if (zero? (g 5))
        (* (g 5) (g 5))
        0))
  (define (</c x) #f))
