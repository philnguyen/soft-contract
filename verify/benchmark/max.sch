(module max
  (provide [max ((integer? integer? . -> . integer?) integer? integer? integer? . -> . integer?)])
  (define (max max2 x y z) (max2 (max2 x y) z)))

(module f (provide [f (integer? integer? . -> . integer?)])
  (define (f x y) (if (>= x y) x y)))

(module main
  (provide [main (->i ([x integer?] [y integer?] [z integer?])
		      (res (x y z) (and/c integer? (λ (m) (= (f x m) m)))))])
  (require max f)
  (define (main x y z)
    (max f x y z)))

(require main)
(main • • •)
