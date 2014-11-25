(module f
  (provide [f ((or/c string? number?) . -> . number?)])
  (define (f x)
    (if (number? x) (add1 x) (string-length x))))

(require f)
(f •)
