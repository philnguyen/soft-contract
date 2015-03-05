(module m racket

  (provide/contract [f (any/c . -> . integer?)])

  (define (f x)
    (+ x 5)))




