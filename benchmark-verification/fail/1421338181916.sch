(module f racket
  (provide (contract-out [f (real? . -> . (and/c real? (>/c 0)))]))
  (define (f n)
    (/ 1 (- 100 n))))
