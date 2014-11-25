(module mult
  (provide [mult (integer? integer? . -> . (and/c integer? (>=/c 0)))]
           [sqr (->i ([n integer?]) (res (n) (and/c integer? (>=/c n))))])
  (define (mult n m)
    (if (or (<= n 0) (<= m 0)) 0
        (+ n (mult n (- m 1)))))
  (define (sqr n) (mult n n)))

(require mult)
(sqr •)
