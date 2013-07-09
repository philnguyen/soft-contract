(module f
  (provide [f ((or/c str? num?) . -> . num?)])
  (define (f x)
    (if (num? x) (add1 x) (str-len x))))

(module g
  (provide [g (any . -> . num?)])
  (require f)
  (define (g x)
    (if (or (num? x) (str? x)) (f x) 0)))

(require g)
(g •)