(module f racket
  (provide/contract [f (any/c . -> . number?)])
  (define (f x)
    (if (number? x) (add1 x) 0)))

(require 'f)
(f •)
