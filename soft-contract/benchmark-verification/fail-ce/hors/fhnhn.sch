(module f racket
  (provide f-spec)
  (define f-spec
    (->i ([x (any/c . -> . integer?)])
	 (res (x)
	      ((and/c (any/c . -> . integer?)
		      (λ (y) (not (and (< (x #f) 0) (< (y #f) 0))))) . -> . integer?)))))

(module h racket
  (provide/contract [h (integer? . -> . (any/c . -> . integer?))])
  (define (h x) (λ (_) x)))

(module g racket
  (provide/contract [g (f-spec integer? . -> . integer?)])
  (require (submod ".." f) (submod ".." h))
  (define (g f n) ((f (h n)) (h n))))

(module main racket
  (provide/contract [main (f-spec integer? . -> . integer?)])
  (require (submod ".." f) (submod ".." g))
  (define (main f m) (g f m)))
