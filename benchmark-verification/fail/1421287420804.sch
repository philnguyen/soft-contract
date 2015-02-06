(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (+ 1.0 0.0000001 (- 100 n))))
