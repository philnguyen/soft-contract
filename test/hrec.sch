(module hrec
  (provide [f ((int? . -> . int?) int? . -> . int?)]
           [main (int? . -> . (and/c int? (or/c zero? positive?)))])
  (define (f g x)
    (if (or (zero? x) (positive? x)) (g x) (f (λ (x) (f g x)) (g x))))
  (define (main n)
    (f add1 n)))

(require hrec)
(main •)