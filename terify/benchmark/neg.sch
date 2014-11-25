(module g (provide [g (integer? . -> . (any/c . -> . integer?))])
  (define (g x) (λ (_) x)))

(module twice
  (provide
   [twice (((any/c . -> . integer?) . -> . (any/c . -> . integer?)) (any/c . -> . integer?) any/c . -> . integer?)])
  (define (twice f x y) ((f (f x)) y)))

(module neg
  (provide [neg ((any/c . -> . integer?) . -> . (any/c . -> . integer?))])
  (define (neg x) (λ (_) (- 0 (x #f)))))

(module main
  (provide [main (integer? . -> . (and/c integer? (>=/c 0)))])
  (require twice neg g)
  (define (main n)
    (if (>= n 0)
        (twice neg (g n) 'unit)
        42)))

(require main)
(main •)
