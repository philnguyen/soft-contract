(module hrec
  (provide [f ((int? . -> . int?) int? . -> . int?)]
           [main (int? . -> . (and/c int? (>=/c 0)))])
  (define (f g x)
    (if (>= x 0) (g x) (f (λ (x) (f g x)) (g x))))
  (define (main n)
    (f add1 n)))

(require hrec)
(main •)