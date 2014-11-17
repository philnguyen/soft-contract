(module assert (provide [assert ((not/c false?) . -> . any)]))

(module m
  (provide [main (-> any)])
  (require assert)
  (define (sum x) (if (<= x 0) 0 (+ x (sum (- x 1)))))
  (define (main) (assert (<= 100 (sum 100)))))

(require m)
(main)