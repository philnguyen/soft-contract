(module f
  (provide [f (cons? . -> . symbol?)])
  (require g)
  (define (f p)
    (if (and (number? (car p)) (number? (cdr p))) (g p) 'no)))

(module g (provide [g ((cons/c number? number?) . -> . symbol?)]))

(require f)
(f •)
