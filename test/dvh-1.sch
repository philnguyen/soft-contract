(module dvh-1
  (provide
   [main ([z : (and/c num? (=/c 5))] . -> . (=/c z))])

  (define (main x) (- (+ x x) x)))

(require dvh-1)
(main •)