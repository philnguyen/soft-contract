(module f
  (provide [f (cons? . -> . number?)])
  (define (f p)
    (if (number? (car p)) (add1 (car p)) 7)))

(require f)
(f •)
