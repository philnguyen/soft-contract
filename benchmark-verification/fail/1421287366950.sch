(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (+ 1.09 (- 100 n))))
