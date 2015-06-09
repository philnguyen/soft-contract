(module zip racket
  (provide/contract
   [main (integer? . -> . (listof any/c))])
  (define (zip xs ys)
    (cond
     [(empty? xs) (cond [(empty? ys) (list)]
			[else 'fail])]
     [else (cond [(empty? ys) (cons (cons (car xs) (car ys)) (zip (cdr xs) (cdr ys)))]
		 [else 'fail])]))
  (define (make-list n)
    (cond [(< n 0) (list)]
	  [else (cons n (make-list (- n 1)))]))
  (define (main n)
    (let ([xs (make-list n)])
      (zip xs xs))))
