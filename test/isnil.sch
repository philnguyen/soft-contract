(module isnil
  (provide [mk-list ([n : int?] . -> .
                     (and/c (listof int?)
                            (λ (l) (if (positive? n) (not (empty? l)) 'admit))))])
  (define (mk-list n)
    (if (zero? n) empty (cons n (mk-list (- n 1))))))
(require isnil)
(mk-list •)