(module mult
  (provide [mult (int? int? . -> . int?)]
           [sqr ([n : int?] . -> . (and/c int? (>=/c n)))])
  (define (mult n m)
    (if (or (zero? n) (negative? n) (zero? m) (negative? m)) 0
        (+ n (mult n (- m 1)))))
  (define (sqr n) (mult n n)))

(require mult)
(sqr •)