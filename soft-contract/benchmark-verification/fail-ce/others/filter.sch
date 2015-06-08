(module filter racket
  (provide/contract
   [filter (([p? (any/c . -> . any/c)] [xs (listof any/c)])
	    . ->i . (res (p? xs)
			 (and/c (listof any/c)
				(λ (ys) (equal? (empty? xs) (empty? ys))))))])
  (define (filter p? xs)
    (cond
      [(empty? xs) empty]
      [else (let ([x (car xs)]
                  [zs (filter p? (cdr xs))])
              (if (p? x) (cons x zs) zs))])))

(require 'filter)
(filter • •)
