(module sum racket
  (provide/contract
   [sum (->i ([n integer?])
	     (res (n) (and/c integer? (>=/c (+ n 1)))))])
  (define (sum n)
    (if (<= n 0) 0
        (+ n (sum (- n 1))))))

(require 'sum)
(sum •)
