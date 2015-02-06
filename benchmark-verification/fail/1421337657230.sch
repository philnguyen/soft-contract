(module f racket
  (provide (contract-out [f (real? . -> . integer?)]))
  (define (f n)
    (/ 1 (- 100 n))))
