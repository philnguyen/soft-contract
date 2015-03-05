(module assert racket (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (integer? . -> . any/c)])
  (require (submod ".." assert))
  (define (mult x y k)
    (if (or (<= x 0) (<= y 0)) (k 0)
        (mult x (- y 1) (acc x k))))
  (define (acc z m) (λ (r) (m (+ z r))))
  (define (check100 w) (assert (<= 600 w)))
  (define (main n) (mult 100 n check100)))
