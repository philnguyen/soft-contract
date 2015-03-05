(module assert racket (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (integer? . -> . any/c)])
  (require (submod ".." assert))
  (define (sum x) (if (<= x 0) 0 (+ x (sum (- x 1)))))
  (define (h y) (assert (<= (+ y y) (sum y))))
  (define (main n) (h n)))
