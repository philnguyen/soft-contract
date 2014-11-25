(module assert (provide [assert ((not/c false?) . -> . any/c)]))

(module m
  (provide [main (-> any/c)])
  (require assert)
  (define (sum x) (if (<= x 0) 0 (+ x (sum (- x 1)))))
  (define (main) (assert (<= 100 (sum 100)))))

(require m)
(main)
