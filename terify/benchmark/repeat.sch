(module repeat
  (provide [repeat
	    (->i ([f (any/c . -> . any/c)]
		  [n integer?]
		  [s : any/c])
		 (res (f n s) (λ (a) (implies (= n 0) (equal? a s)))))])
  (define (repeat f n s)
    (if (= n 0) s (f (repeat f (- n 1) s)))))

(require repeat)
(repeat • • •)
