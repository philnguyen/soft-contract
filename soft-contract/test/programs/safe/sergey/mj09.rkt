; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/mj09.sch
#lang racket

(require soft-contract/fake-contract)

(let ([h (λ (b)
	   (let ([g (λ (z) z)])
	     (let ([f (λ (k)
			(if b
			    (k 1)
			    (k 2)))])
	       (let ([y (f (λ (x) x))])
		 (g y)))))])
  (let* ([x (h #t)]
	 [y (h #f)])
    y))
