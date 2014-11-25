(module dvh-1
  (provide
   [main (->i ([z (and/c number? (=/c 5))])
	      (res (z) (=/c z)))])

  (define (main x) (- (+ x x) x)))

(require dvh-1)
(main •)
