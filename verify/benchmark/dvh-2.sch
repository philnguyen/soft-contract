(module dvh-2 racket
  (provide/contract
   [main (->i ([x number?])
	      (res (x) (->i ([y (and/c number? (=/c x))])
			    (res (y) (=/c x)))))])

  (define (main x) (lambda (y) y)))

(require 'dvh-2)
((main •) •)
