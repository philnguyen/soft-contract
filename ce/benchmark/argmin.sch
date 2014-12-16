(module holes
  (provide [proc (-> any/c number?)]
	   [lst (nelistof any/c)]))

(module min
  (provide [min (real? real? . -> . real?)])
  (define (min x y)
    (if (< x y) x y)))

(module argmin
  (provide [argmin ((-> any/c number?) (nelistof any/c) . -> . any/c)])
  (require min)
  (define (argmin f xs)
    (cond [(empty? (cdr xs)) (f (car xs))]
	  [else (min (f (car xs))
		     (argmin f (cdr xs)))])))

(require holes argmin)
(argmin proc lst)
