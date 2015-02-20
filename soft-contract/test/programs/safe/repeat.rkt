#lang racket
(require soft-contract/fake-contract)

(define (repeat f n s)
  (if (= n 0) s (f (repeat f (- n 1) s))))

(provide/contract
   [repeat (->i ([f (any/c . -> . any/c)] [n integer?] [s any/c])
		(res (f n s) (λ (a) (implies (= n 0) (equal? a s)))))])
