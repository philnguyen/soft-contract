(module f
  (provide [f (cons? . -> . num?)])
  (define (f p)
    (if (num? (car p)) (add1 (car p)) 7)))

(require f)
(f •)