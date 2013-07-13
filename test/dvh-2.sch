(module dvh-2
  (provide
   [main ([x : num?] . -> . ([y : (and/c num? (lambda (y) (= y x)))] . -> . (lambda (z) (= x z))))])

  (define (main x) (lambda (y) y)))

(require dvh-2)
((main •) •)