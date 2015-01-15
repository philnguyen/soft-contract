(module sqr racket
  (provide 
   (contract-out 
    [sqr (integer? . -> . (and/c integer? (lambda (x) (> x 0))))]))

  (define (sqr n)
    (* n n)))
