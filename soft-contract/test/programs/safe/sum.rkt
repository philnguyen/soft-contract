#lang racket
(require soft-contract/fake-contract)

(define (sum n)
  (if (<= n 0) 0
      (+ n (sum (- n 1)))))

(provide/contract [sum (->i ([n integer?])
			    (res (n) (and/c integer? (>=/c n))))])
