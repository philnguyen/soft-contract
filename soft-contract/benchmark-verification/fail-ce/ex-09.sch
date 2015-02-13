(module f racket
  (provide/contract [f ((or/c string? number?) . -> . number?)])
  (define (f x)
    (if (number? x) (add1 x) (string-length x))))

(module g racket
  (provide/contract [g (any/c . -> . number?)])
  (require (submod ".." f))
  (define (g x)
    (f x)))

(require 'g)
(g •)
