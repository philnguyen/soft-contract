(module f racket
  (provide (contract-out [f ((and/c integer? (not (=/c 100))) . -> . integer?)]))
  (define (f n)
    (/ 1 (- 100 n))))
