(module m racket
  (define (f x) x)
  (provide 
   (contract-out 
    [f (-> (lambda (x) (>= x 0)) any/c)])))
