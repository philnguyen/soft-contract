(module mult
  (provide [mult (int? int? . -> . (and/c int? (>=/c 0)))]
           [sqr ([n : int?] . -> . (and/c int? (>=/c n)))])
  (define (mult n m)
    (if (or (<= n 0) (<= m 0)) 0
        (+ n (mult n (- m 1)))))
  (define (sqr n) (mult n n)))

(require mult)
(sqr •)