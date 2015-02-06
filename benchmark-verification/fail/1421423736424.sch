(module f racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . not)]))
  (define (f g)
    (not (= (g 5) (g 7)))))
