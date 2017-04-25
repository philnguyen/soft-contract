#lang racket
(require soft-contract/fake-contract)

(define (tak x y z k)
  (if (not (< y x))
      (k z)
      (tak (- x 1)
	   y
	   z
	   (lambda (v1)
	     (tak (- y 1)
		  z
		  x
		  (lambda (v2)
		    (tak (- z 1)
			 x
			 y
			 (lambda (v3)
			   (tak v1 v2 v3 k)))))))))

(define (tak-main x y z)
  (tak x y z (λ (x) x)))

(provide/contract
 [tak-main (integer? integer? #|HERE|# number? . -> . integer?)])
