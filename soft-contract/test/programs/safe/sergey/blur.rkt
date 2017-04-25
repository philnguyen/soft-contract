; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/blur.sch
#lang racket

(require soft-contract/fake-contract)

(define id (λ (x) x))
(define blur (λ (y) y))
(define lp
  (λ (a)
    (λ (n)
      (if (zero? n)
	  (id a)
	  (let* ([r ((blur id) #t)]
		 [s ((blur id) #f)])
	    (not (((blur lp) s) (sub1 n))))))))

((lp #f) 2)
