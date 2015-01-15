(module f racket
  (provide (contract-out [f ((</c 0) . -> . real?)]))
  (define (f n)
    (/ 1 (- 100 n))))
