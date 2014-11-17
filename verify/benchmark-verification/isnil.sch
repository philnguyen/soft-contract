(module isnil
  (provide [mk-list ([n : int?] . -> .
                     (and/c (listof int?)
                            (λ (l) (implies (> n 0) (cons? l)))))])
  (define (mk-list n)
    (if (= n 0) empty (cons n (mk-list (- n 1))))))
(require isnil)
(mk-list •)