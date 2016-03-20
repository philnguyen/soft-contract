; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/kcfa3.sch
#lang racket

(require soft-contract/fake-contract)

((λ (f1)
   (let ((a (f1 #t)))
     (f1 #f)))
 (λ (x1)
   ((λ (f2)
      (let ((b (f2 #t)))
	(f2 #f)))
    (λ (x2)
      ((λ (f3)
	 (let ((c (f3 #t)))
	   (f3 #f)))
       (λ (x3)
	 ((λ (z) (z x1 x2 x3))
	  (λ (y1 y2 y3) y1))))))))
