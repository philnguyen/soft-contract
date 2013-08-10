(module dvh-2
  (provide
   [main ([x : num?] . -> . ([y : (and/c num? (=/c x))] . -> . (=/c x)))])

  (define (main x) (lambda (y) y)))

(require dvh-2)
((main •) •)