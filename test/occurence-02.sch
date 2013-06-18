(module f
  (provide [f ((or/c str? num?) . -> . num?)])
  (define (f x)
    (if (num? x) (add1 x) (str-len x))))

(require f)
(f •)