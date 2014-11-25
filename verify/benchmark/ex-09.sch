(module f
  (provide [f ((or/c string? number?) . -> . number?)])
  (define (f x)
    (if (number? x) (add1 x) (string-length x))))

(module g
  (provide [g (any/c . -> . number?)])
  (require f)
  (define (g x)
    (if (let ([tmp (number? x)])
          (if tmp tmp (string? x)))
        (f x)
        0)))

(require g)
(g •)
