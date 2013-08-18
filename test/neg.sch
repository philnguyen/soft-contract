(module g (provide [g (int? . -> . (any . -> . int?))])
  (define (g x) (λ (_) x)))

(module twice
  (provide
   [twice (((any . -> . int?) . -> . (any . -> . int?)) (any . -> . int?) any . -> . int?)])
  (define (twice f x y) ((f (f x)) y)))

(module neg
  (provide [neg ((any . -> . int?) . -> . (any . -> . int?))])
  (define (neg x) (λ (_) (- 0 (x #f)))))

(module main
  (provide [main (int? . -> . (and/c int? (>=/c 0)))])
  (require twice neg g)
  (define (main n)
    (if (>= n 0)
        (twice neg (g n) 'unit)
        42)))

(require main)
(main •)