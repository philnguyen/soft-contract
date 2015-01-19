(module f racket
  (provide/contract [f (any/c any/c . -> . number?)])
  (define (f x y)
    (if (if (number? x) (string? y) #f)
        (+ x (string-length y))
        0)))

(require 'f)
(f • •)
