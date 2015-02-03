(module isnil racket
  (provide/contract [mk-list (->i ([n integer?])
			 (res (n)
			      (and/c (listof integer?)
				     (λ (l) (implies (> n 0) (cons? l))))))])
  (define (mk-list n)
    (if (= n 0) empty (cons n (mk-list (- n 1))))))
(require 'isnil)
(mk-list •)
