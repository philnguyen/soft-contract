(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (if (not (zero? n))
    (/ 1 (- 100 n))
        0)))
