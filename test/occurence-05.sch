(module f
  (provide [f (any any . -> . num?)])
  (define (f x y)
    (if (and (num? x) (str? y)) (+ x (str-len y)) 0)))

(require f)
(f • •)