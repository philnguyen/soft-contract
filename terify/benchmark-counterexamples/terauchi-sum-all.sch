(module assert (provide [assert ((not/c false?) . -> . any)]))

(module m
  (provide [main (-> any)])
  (require assert)
  (define (sum x) (if (<= x 0) 0 (+ x (sum (- x 1)))))
  (define (h y) (assert (<= y (sum y))))
  (define (main) (h 0)))

(require m)
(main)