(module f racket
  (provide/contract [f (integer? . -> . integer?)])
  (define (f n)
    (/ 1 (- 100 n))))

(+ 1 "hi")
