(module f racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . (lambda (x) x))]))
  (define (f g)
    (= (g 5) (g (lambda (r) r)))))
