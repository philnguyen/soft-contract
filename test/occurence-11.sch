(module f
  (provide [f (cons? . -> . symbol?)])
  (require g)
  (define (f p)
    (if (and (num? (car p)) (num? (cdr p)))
        (g p)
        'no)))

(module g
  (provide [g ((cons/c num? num?) . -> . symbol?)]))

(require f)
(f •)