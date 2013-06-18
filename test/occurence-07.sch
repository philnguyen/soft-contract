(module f
  (provide [f (any any . -> . num?)])
  (define (f x y)
    (if (if (num? x) (str? y) #f)
        (+ x (str-len y))
        0)))

(require f)
(f • •)