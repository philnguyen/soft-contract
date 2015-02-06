(module f racket
  (provide/contract [f (integer? . -> . integer?)])
  (define (f n)
    (/ 2 (+ 1 (* n n)))))
