(module f racket
  (provide/contract 
    [f (integer? . -> . integer?)])
  (define (f n)
    (if (= n 0) 1
    (/ 1 (- 100 n)))))


