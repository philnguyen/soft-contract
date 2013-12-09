(module m
  (provide [f (int? . -> . int?)])
  (define (f n)
    (if (= n 0) "" (str-len (f (- n 1))))))
(require m)
(f •)