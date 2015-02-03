(module mem racket
  (provide/contract
   [mk-list (->i ([_ integer?] [x integer?])
		 (res (_ x) (and/c (listof integer?)
				   (λ (l) (or (empty? l) (mem x l))))))]
   [mem (integer? (listof integer?) . -> . boolean?)])
  (define (mk-list n x)
    (if (< n 0) empty (cons x (mk-list (- n 1) x))))
  (define (mem x xs)
    (if (empty? xs) #f (or (= x (car xs)) (mem x (cdr xs))))))

(require 'mem)
(mk-list • •)
