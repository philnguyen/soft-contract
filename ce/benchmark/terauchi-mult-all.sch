(module assert racket (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (-> any/c)])
  (require (submod ".." assert))
  (define (mult x y)
    (if (or (<= x 0) (<= y 0)) 0 (+ x (mult x (- y 1)))))
  (define (h y) (assert (<= y (mult y y))))
  (define (main) (h 0)))

(require 'm)
(main)
