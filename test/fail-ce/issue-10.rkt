(module f racket
  (provide/contract [f ((lambda (x) #t) . -> . integer?)])
  (define (f n)
    (/ 1 (- 100 n))))
