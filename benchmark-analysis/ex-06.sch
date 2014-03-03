(module f
  (provide [f ((or/c num? str?) str? . -> . num?)])
  (define (f x y)
    (if (and (num? x) (str? y))
        (+ x (str-len y))
        (str-len x))))

(require f)
(f • •)