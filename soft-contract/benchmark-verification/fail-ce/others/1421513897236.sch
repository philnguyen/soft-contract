(module m racket
  (provide (contract-out [f (->i ([x integer?]) [res (x) integer?])]))
  (define (f n)
    (/ 1 (- 100 n))))
