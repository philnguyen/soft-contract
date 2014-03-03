(module ex-13
  (provide [f (any any . -> . true?)])
  (define (f x y)
    (cond
      [(and (num? x) (str? y)) (and (num? x) (str? y))]
      [(num? x) (and (num? x) (not (str? y)))]
      [else (not (num? x))])))
(require ex-13)
(f • •)