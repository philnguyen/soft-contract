(module f racket
  (provide/contract [f (any/c any/c . -> . number?)])
  (define (f x y)
    (if (and (number? x) (string? y)) (+ x (string-length y)) 0)))

(require 'f)
(f • •)
