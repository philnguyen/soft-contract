(module g racket
  (provide/contract [g (integer? . -> . (any/c . -> . integer?))])
  (define (g x) (λ (_) x)))

(module twice racket
  (provide/contract
   [twice (((any/c . -> . integer?) . -> . (any/c . -> . integer?)) (any/c . -> . integer?) any/c . -> . integer?)])
  (define (twice f x y) ((f (f x)) y)))

(module neg racket
  (provide/contract [neg ((any/c . -> . integer?) . -> . (any/c . -> . integer?))])
  (define (neg x) (λ (_) (- 0 (x #f)))))

(module main racket
  (provide/contract [main (integer? . -> . (and/c integer? (>=/c 0)))])
  (require (submod ".." twice) (submod ".." neg) (submod ".." g))
  (define (main n)
    (if (>= n 0)
        (twice neg (g n) 'unit)
        42)))

(require 'main)
(main •)
