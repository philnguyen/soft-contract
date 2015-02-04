(module f racket
  (provide/contract [f (any/c any/c . -> . number?)])
  (define (f x y)
    (+ x (string-length y))))

(require 'f)
(f • •)
