(module f racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . (lambda (x) x))]))
  (define (f g)
    (not (= (g 5) (g 7)))))
