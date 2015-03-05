(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (if (> n 100)
    (/ 1 (- 100 n))
        2))) 
