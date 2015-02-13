(module f racket
  (provide/contract [f (->i ([x (any/c . -> . integer?)])
		   (res (x)
			((and/c (any/c . -> . integer?)
				(λ (y) (not (and (> (x #f) 0) (< (y #f) 0))))) . -> . integer?)))]))

(module h racket
  (provide/contract [h (integer? . -> . (any/c . -> . integer?))])
  (define (h x) (λ (_) x)))

(module g racket
  (provide/contract [g (integer? . -> . integer?)])
  (require (submod ".." f) (submod ".." h))
  (define (g n) ((f (h n)) (h n))))

(module main racket
  (provide/contract [main (integer? . -> . integer?)])
  (require (submod ".." g))
  (define (main m) (g m)))

(require 'main)
(main •)
