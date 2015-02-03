#lang racket
(require soft-contract/fake-contract)

(define (append xs ys)
  (if (empty? xs) ys
      (cons (car xs) (append (cdr xs) ys))))

(define (reverse xs)
  (if (empty? xs) empty
      (append (cdr xs) (cons (car xs) empty))))


(provide/contract
 [reverse (->i ([xs (listof any/c)])
	       (res (xs)
		    (and/c (listof any/c)
			   (λ (ys) (equal? (empty? xs) (empty? ys))))))]
 [append ((listof any/c) (listof any/c) . -> . (listof any/c))])
