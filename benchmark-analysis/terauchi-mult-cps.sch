(module assert (provide [assert ((not/c false?) . -> . any)]))

(module m
  (provide [main (-> any)])
  (require assert)
  (define (mult x y k)
    (if (or (<= x 0) (<= y 0)) (k 0)
        (mult x (- y 1) (acc x k))))
  (define (acc z m) (λ (r) (m (+ z r))))
  (define (check100 w) (assert (<= 100 w)))
  (define (main) (mult 100 100 check100)))

(require m)
(main)