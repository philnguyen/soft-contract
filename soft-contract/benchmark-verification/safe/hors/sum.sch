(module sum racket
  (provide/contract
   [sum (->i ([n integer?])
	     (res (n) (and/c integer? (>=/c 0))))])
  (define (sum n)
    (if (<= n 0) 0
        (+ n (sum (- n 1))))))

(require 'sum)
(sum •)
