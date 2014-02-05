(module ho ; real pos
  (provide
   [f1 (([x : (and/c int? (>/c 0))] . -> . (and/c int? (>=/c x))) . -> . (>/c 0))])
  (define (f1 g) (- (g 0) 5)))

(require ho)
(• f1)