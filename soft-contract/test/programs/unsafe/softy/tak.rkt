#lang racket
(require soft-contract/fake-contract)

(define (tak x y z)
  (if (false? (< y x)) z
      (tak (tak (- x 1) y z)
	   (tak (- y 1) z x)
	   (tak (- z 1) x y))))

(provide/contract
 [tak (integer? integer? #|HERE|# number? . -> . integer?)])
