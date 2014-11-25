(module f
  (provide [f ((or/c number? string?) string? . -> . number?)])
  (define (f x y)
    (if (and (number? x) (string? y))
        (+ x (string-length y))
        (string-length x))))

(require f)
(f • •)
