(module dvh-1
  (provide
   [main ([z : (and/c num? (lambda (q) (= q 5)))] . -> . (lambda (y) (= y z)))])

  (define (main x) (- (+ x x) x)))

(require dvh-1)
(main •)