(module zip racket
  (provide/contract [zip (([x integer?] [y integer?]) . ->i . (res (x y) (if (= x y) integer? any/c)))])
  (define (zip x y)
    (cond
      [(and (= x 0) (= y 0)) x]
      [(and (not (= x 0)) (not (= y 0))) (+ 1 (zip (- x 1) (- y 1)))]
      [else 'fail])))

(module map racket
  (provide/contract [map (integer? . -> . integer?)])
  (define (map x)
    (if (= x 0) x (+ 1 (map (- x 1))))))

(module main racket
  (provide/contract [main (->i ([n integer?])
		      (res (n) (and/c integer? (=/c n))))])
  (require (submod ".." zip) (submod ".." map))
  (define (main n) (map (zip n n))))
