(module f racket
  (provide/contract [f (any/c . -> . number?)])
  (define (f x)
    (if (number? x) 0 #|HERE|# (add1 x))))

(require 'f)
(• f)
