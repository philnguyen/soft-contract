(module max racket
  (provide/contract [max ((integer? integer? . -> . integer?) integer? integer? integer? . -> . integer?)])
  (define (max max2 x y z) #|HERE|# (max2 y z)))

(module f racket
  (provide/contract [f (integer? integer? . -> . integer?)])
  (define (f x y) (if (>= x y) x y)))

(module main racket
  (provide/contract [main (->i ([x integer?] [y integer?] [z integer?])
		      (res (x y z) (and/c integer? (λ (m) (= (f x m) m)))))])
  (require (submod ".." max) (submod ".." f))
  (define (main x y z)
    (max f x y z)))

(require 'main)
(main • • •)
