(module ex-13
  (provide [f (any/c any/c . -> . true?)])
  (define (f x y)
    (cond
      [(and (number? x) (string? y)) (and (number? x) (string? y))]
      [(number? x) (and (number? x) (not (string? y)))]
      [else (not (number? x))])))
(require ex-13)
(f • •)
