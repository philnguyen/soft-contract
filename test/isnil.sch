(module isnil
  (provide [mk-list ([n : int?] . -> .
                     (and/c (listof int?)
                            (λ (l) (implies (positive? n) (not (empty? l))))))])
  (define (mk-list n)
    (if (zero? n) empty (cons n (mk-list (- n 1))))))
(require isnil)
(mk-list •)