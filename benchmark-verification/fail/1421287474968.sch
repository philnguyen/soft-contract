(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (+ 1.0 (- 100 n) (* 2 (/ 1 n)))))
