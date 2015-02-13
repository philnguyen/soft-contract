(module m racket
  (provide (contract-out [f ((integer? . -> . integer?) . -> . (lambda (x) x))]))
  (define (f x) (not (= (x 5) (x 5)))))
