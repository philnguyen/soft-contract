; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/kcfa2.sch
#lang racket
(require soft-contract/fake-contract)

((λ (f1)
   (let ((a (f1 #t)))
     (f1 #f)))
 (λ (x1)
   ((λ (f2)
      (let ((b (f2 #t)))
	(let ((c (f2 #f)))
	  (f2 #t))))
    (λ (x2) ((λ (z) (z x1 x2)) (λ (y1 y2) y1))))))
