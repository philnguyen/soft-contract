(module assert racket (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (-> any/c)])
  (require (submod ".." assert))
  (define (sum x) (if (<= x 0) 0 (+ x (sum (- x 1)))))
  (define (h y) (assert (<= y (sum y))))
  (define (main) (h 0)))

(require 'm)
(main)
