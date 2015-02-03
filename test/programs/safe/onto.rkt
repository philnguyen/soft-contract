#lang racket
(require soft-contract/fake-contract)

(define (onto A)
  (λ (callbacks)
     (λ (f)
        (λ (obj)
	   (if (false? f) (cons obj callbacks)
	       (let ([cb (if (string? f) (obj f) f)])
		 (cons (λ () (cb obj)) callbacks)))))))

(provide/contract
   [onto (->i ([A (any/c . -> . boolean?)]) ; poor man's quantifier
	      (res (A)
		   (->i ([callbacks (listof procedure?)])
			(res (callbacks)
			     (->i ([f (or/c false? string? (A . -> . any/c))])
				  (res (f)
				       (->i ([obj (and/c
						   A
						   (cond
						    [(false? f) (any/c . -> . any/c)]
						    [(string? f) (->i ([k any/c]) (res (k) (if (equal? k f) (A . -> . any/c) any/c)))]
						    [else any/c]))])
					    (res (obj) (listof procedure?)))))))))])
