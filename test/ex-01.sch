(module f
  (provide [f (any . -> . num?)])
  (define (f x)
    (if (num? x) (add1 x) 0)))

(require f)
(f •)