(module f racket
  (provide (contract-out [f ((integer? . -> . any/c) . -> . (lambda (x) x))]))
  (define (f g)
    (= (g 5) (g 5))))
